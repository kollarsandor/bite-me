# Reversible Scatter Flow (RSF) – Teljes Dokumentáció

---
Summary:
Az RSF (Reversible Scatter Flow) egy újszerű neurális hálózati architektúra, amely kizárólag egy invertálható affin csatolás primitívre (split → scale → translate) épül, O(1) memória-komplexitással a backward pass során.

 Alapvető Struktúra

Az RSF teljes mértékben mentes a hagyományos komponensektől, mint self-attention, MLP blokkok, konvolúciók vagy LayerNorm; a LayerCore csupán négy tenzort használ (s_weight, t_weight, s_bias, t_bias) a skálázáshoz és eltoláshoz. A forward pass szekvenciálisan számolja a scale-t x2-ből, alkalmazza y1-re, majd trans-t a módosított y1-ből y2-höz adva – ez kereszt-csatolásként erősebb interakciót teremt, mint a RealNVP párhuzamos verziója. Az invertálhatóság futásidőben ellenőrizhető (forwardOnCore → inverseOnCore), és formálisan verifikált Lean 4, Mizar, Twelf, Beluga rendszerekkel, garantálva a bijektivitást anélkül, hogy aktivációkat tárolna.

A scatter mechanizmus (rsf_scatter, Orthogonal Fractal Transform Block) fraktál-keverést végez 1/√2 skálázással, biztosítva a dimenziók közötti információáramlást anélkül, hogy permutációra vagy maszkolásra szorulna, ellentétben a NICE/RealNVP/Glow modellekkel, amelyek belső MLP/ResNet blokkokat használtak a s/t függvényekhez.

 Hardveres Előnyök

Zig nyelven íródott a kódbázis (rsf.zig), közvetlen CUDA/Futhark integrációval, pinned memory és aszinkron DMA-val, kihagyva a PyTorch/Python overheadet; F16 konverzió natívan történik GPU tolás előtt. Kompatibilis NVIDIA B200/B300 hardverrel (default_group_size=256, 8 CUDA warp), tenzormagok F16/F32-rel maximálisan kihasználva, FlashAttention nélkül, mivel nincs O(N²) attention mátrix – IO-bound problémák kizárva. A backward O(1) memóriája lehetővé teszi akár 10 000+ rétegű traininget azonos VRAM-mal, szemben Transformer/Mamba O(L) igényével.

Production-ready elemek: CRC32 checkpointok, NCCL allReduce, ModalGPUClient felhő telepítés.

 Különbségek Elődöktől

RealNVP/Glow/NICE generatív flow-ként használták az affin csatolást (y1 = x1 ⊙ exp(s(x2)), y2 = x2 + t(x1)), de belső komplex hálózatokkal (ResNet/MLP) a s/t-hez; RSF ezeket eltávolítja, egyetlen mátrix-vektor szorzást (W·x + b) használva, diszkriminatív LLM kontextusra szabva. Mamba eltűnt 2025-re reasoning feladatokon, hibridizve Transformerrel; RSF чисто O(1) stack-el skálázódik korlát nélkül. RevNet/Reformer wrapper-ek, RSF ontológiailag puritán: egyetlen primitív a gyökér.

| Architektúra | Primitív | Memória Backward | Belső Hálózatok | Cél |
|--------------|----------|-------------------|-----------------|-----|
| RealNVP/Glow | Affin coupling | O(L) | Igen (MLP/ResNet) | Generatív |
| Transformer | Self-attention | O(L) | Igen (MLP) | Diszkriminatív |
| Mamba | SSM scan | O(L) | - | Hibrid |
| RSF | Cross-affine + scatter | O(1) | Nem | Diszkriminatív/LLM |

 Paradigma Állapot

RSF a 5. gyökér-architektúra (Perceptron, CNN, RNN, Transformer után): ontológiailag új, kizárólagos primitívvel, 100% információ-megőrzéssel (invertálható), Curry-Howard alapján verifikált tézként. Nem igényel ökoszisztémát induláskor (mint Transformer 2017-ben); ha skálázódik, forradalmasítja exascale LLM traininget költségcsökkentéssel. Teljesítmény empirikusan igazolandó, de státusz a kódból fakad.

Ez a puritán dizájn determinisztikus áramlást biztosít, felrobbantva a memória-mítoszt anélkül, hogy speciális kernelre szorulna.

## I. RÉSZ: Elméleti Alapok és Architekturális Értékelés

### Bevezetés: A Számítási Primitívek Evolúciója és az Információvesztés Dogmája

A mesterséges intelligencia és azon belül a mélytanulás fejlődéstörténete alapvető paradigmaváltások sorozataként írható le. Ezek az ugrásszerű fejlődési pontok történelmileg mindig új „gyökérszintű" számítási primitívek bevezetésével jártak, amelyek meghaladták a korábbi rendszerek alapvető matematikai vagy reprezentációs korlátait:

- **1958 – Perceptron:** A lineáris szeparálhatóság alapköveinek lefektetése, teljesen új fogalom a gépi tanulás hajnalán.
- **1989 – CNN (LeNet):** A lokális térbeli invariancia és a súlymegosztás önálló építőelemként, forradalmasítva a gépi látást.
- **1997 – LSTM:** A szekvenciális időbeli függőségek és az eltűnő gradiens problémájának kezelése kapumechanizmusokon keresztül.
- **2017 – Transformer:** A globális kontextuális figyelem önálló építőelemként, amely teljesen felváltotta a rekurrenciát és a konvolúciót.
- **RSF – Az Ötödik Paradigma:** Egy új, független számítási keret, amely szakít az elmúlt évtizedek hagyományos építőelemeivel és egy ötödik, teljesen autonóm paradigmát kínál.

A klasszikus mélytanulás szinte dogmaszerűen épül arra az alapfeltevésre, hogy egy neurális hálózat szükségképpen **információveszteséges folyamat**. A hagyományos architektúrák – nemlineáris aktivációkon (pl. ReLU, amely a negatív tartományt nullára vágja), dimenziócsökkentő pooling rétegeken és komplex normalizációs eljárásokon keresztül – minden egyes rétegátmenet során az információ jelentős részét megsemmisítik. Ennek a matematikai pusztításnak rendkívül súlyos, iparági szintű következménye van: a gradiens visszaterjesztés során a láncszabály alkalmazása nélkülözhetetlenné teszi a köztes aktivációs állapotok memóriában való tárolását. Ahogy a modellek rétegszáma és kontextusablaka növekszik, ez az aktivációs memória hatalmas szűk keresztmetszetté válik, amelyre eddig csak mérnöki „trükköket" (pl. gradient checkpointing vagy offloading) fejlesztettek ki, de az alapvető elméleti probléma megoldatlan maradt.

Az RSF ezzel szemben kizárólag affin kapcsolásra és szóró műveletekre épített, **matematikailag pontosan invertálható primitívet** vezet be, amely elveti az információpusztítás paradigmáját.

---

### A Hagyományos Építőelemek Radikális Dekonstrukciója

A modern mélytanulási modellek, beleértve a legfejlettebb LLM-eket is, jól bevált, szabványosított eszközkészletre épülnek. A Transformer koncepció a *„Figyelem minden, ami szükséges"* elvét hirdette, mégis a gyakorlatban komplex, heterogén mikro-architektúrát alkalmazott: a query-key-value alapú önfigyelem mellett masszív többrétegű perceptronokat (MLP), rétegnormalizációt (LayerNorm) és pozicionális kódolást is integrált.

Az RSF analóg logikát követ, de még radikálisabb purifikációt hajt végre: az affin kapcsolást (amely korábban a Normalizing Flow generatív modellek – NICE, RealNVP – nagyobb ökoszisztémájának része volt) **kiemeli kontextusából és egyetlen, kizárólagos számítási primitívvé teszi**.

#### A Figyelemmechanizmus és a Konvolúció Elhagyása

A figyelemmechanizmus inherensen $O(N^2)$ komplexitású a szekvenciahosszra nézve. Bár ez rendkívül sikeresnek bizonyult a nyelvmodellezésben, az RSF teljes mértékben elveti ezt a megközelítést. Nem alkalmaz query-key mátrixszorzást és nem használ softmax-alapú normalizációt.

Az információ keverését az RSF-ben egy **determinisztikus „scatter" (szóró) művelet** végzi. Ez topológiailag garantálja az információ akadálytalan áramlását anélkül, hogy az input-függő, dinamikus útválasztás drága számítási költségeit kellene fizetni. A `rsf_scatter` függvény Futhark kernelekben pillangó-művelettel keveri a bemeneteket inverz négyzetgyök kettő skálázással, hasonlóan egy Haar-transzformhoz:

- Egyik vektorfél: $\text{inv\_sqrt2} \cdot (x[j] + x[j + \text{half}])$ (összegek)
- Másik vektorfél: $\text{inv\_sqrt2} \cdot (x[j] - x[j + \text{half}])$ (különbségek)

ahol $\text{inv\_sqrt2} = 1/\sqrt{2}$. Ez a strukturális keverés minden rétegben permutálja a dimenziókat, lehetővé téve a teljes kontextus modellezését drága figyelemmátrixok kiszámítása nélkül.

Hasonlóképpen hiányoznak az architektúrából a **konvolúciós szűrők és a hagyományos előrecsatolt hálózatok (MLP)**. Az RSF esetében a súlymátrixok kizárólag az affin kapcsolás skálázási és transzlációs paramétereinek generálásáért felelnek, ezzel jelentősen növelve a paraméterhatékonyságot és a matematikai értelmezhetőséget.
<img width="1254" height="1254" alt="image" src="https://github.com/user-attachments/assets/d921818e-5ad1-4a18-84dc-f17015af4ab3" />

#### A Normalizációs Rétegek és Hagyományos Aktivációs Függvények Eltávolítása

Az RSF esetében a numerikus stabilitást és az információáramlást **maga a modell alapvető geometriája garantálja**. A szimmetrikus affin kapcsolás inherensen korlátozza a variancia elszabadulását a topológiai struktúra miatt – nincs szükség mesterséges, iteratív statisztikai normalizációra.

A klasszikus aktivációs függvények (ReLU, GELU, Swish) alapvető természete az, hogy információt pusztítanak. Az RSF ezzel szemben az $\exp(\text{clip}(\cdot))$ függvényt használja, amely **nem egy rétegek közé illesztett önálló modul, hanem az affin kapcsolás skálázó ágának szerves, elválaszthatatlan része**. Ez a művelet szigorúan monoton növő, ezért analitikusan invertálható. A `clip` függvény (amely a `LayerCore` Zig modulban az alapértelmezett `clip_min = -5.0` és `clip_max = 5.0` határok közé vágja a belső alapösszeget) globális numerikus stabilitást garantál.

#### Gyökérszintű Architektúrák Összehasonlítása

| Architektúra | Alapítás | Térbeli/Szekvenciális Kezelés | Nemlinearitás | Normalizáció | Invertálhatóság |
|---|---|---|---|---|---|
| Perceptron | 1958 | Független dimenziók | Küszöbfüggvény | Nincs | Nincs |
| CNN | 1989 | Lokális Konvolúció | ReLU / Tanh | BatchNorm | Nincs |
| LSTM | 1997 | Temporális rekurzió, Kapuk | Sigmoid / Tanh | Ritkán | Nincs |
| Transformer | 2017 | Pozicionális kódolás / Figyelem | MLP (GELU/ReLU) | LayerNorm | Nincs |
| **RSF** | **Új** | **Globális Scatter** | $\exp(\text{clip}(\cdot))$ | **Nincs** | **Garantáltan Egzakt** |

---

### Az Affin Kapcsolás Matematikai Formalizmusa és Differenciálgeometriai Dinamikája

A hagyományos paradigmában egy réteg kimenete az $y = f(Wx + b)$ általános alakban írható, ahol $f$ egy nemlineáris, egyirányú és gyakran nem invertálható leképezés. Az RSF ezzel szemben egy teljesen eltérő differenciálgeometriai és dinamikai rendszert alkalmaz, amely közelebb áll az ideális folyadékok áramlását leíró matematikához.

#### Az Előremeneti Menet Pontos Egyenletei

A folyamat egy $x$ bemeneti vektor transzformációjával kezdődik, amelyet a rendszer a „scatter" művelet után két egyenlő részre oszt: $(x_1, x_2)$.

**1. A skálafaktor kiszámítása** – A hálózat először egy skálázó vektort ($s$) számít az $x_2$ komponensből:

$$s = \exp(\text{clip}(W_s x_2 + b_s, \text{min}, \text{max}))$$

A Lean 4 kódbázisban ez a `computeScaleInto` függvény logikájának felel meg. Az $s$ vektor kizárólag az $x_2$ állapottól függ.

**2. Az $x_1$ komponens skálázása** – elemenkénti szorzás:

$$y_1 = x_1 \odot s$$

Ez az aszimmetrikus, keresztirányú módosítás elméletileg kulcsfontosságú. Mivel a skálázás csak $x_2$-ből származik, az $y_1$ parciális deriváltja $x_1$-re vonatkozóan diagonális mátrix lesz. Ez drasztikusan egyszerűsíti a számításokat és elkerüli a Jacobi-mátrix drága determináns-számításait.

**3. A transzlációs faktor kiszámítása és $x_2$ módosítása**:

$$t = W_t y_1 + b_t$$
$$y_2 = x_2 + t$$

A réteg végső kimenete az összefűzött $(y_1, y_2)$ vektor.

#### Az Inverz Menet Tökéletes Szimmetriája

A fenti rendszer legfontosabb, forradalmi matematikai tulajdonsága a **determinisztikus és veszteségmentes invertálhatóság**. Az `InverseInPlace` függvény az alábbi inverz lépéseket hajtja végre:

**$x_2$ visszaállítása** – mivel $t$ kiszámítása csak $y_1$-en alapult:

$$t = W_t y_1 + b_t \quad\Rightarrow\quad x_2 = y_2 - t$$

**$x_1$ visszaállítása** – $s$ újra deterministikusan generálható $x_2$-ből:

$$s = \exp(\text{clip}(W_s x_2 + b_s)) \quad\Rightarrow\quad x_1 = y_1 \oslash s$$

Ez a lenyűgöző szimmetria – ahol a matematikai képlet lényegében saját inverze, csupán a szorzás/összeadás operátorai cserélődnek osztásra/kivonásra – az RSF lelke. A Lean 4 formális bizonyítási környezetben implementált `ThForwardInverseIdentity` tétel deduktívan és cáfolhatatlanul verifikálja a topológiai bijekciót: `InverseOnCore(C, ForwardOnCore(C, x)) = x`.

---

### A Globális $O(1)$ Memóriaigény Paradigmája

#### A Hagyományos Memóriafogyasztás Hardverproblémája

Egy hagyományos hálózatnál a memóriaigény közvetlenül arányos a hálózat mélységével: $O(N \cdot B \cdot S \cdot D)$. Az ipar eddig csak „mérnöki trükkökkel" próbálta áthidalni ezt:

- **Gradient Checkpointing** – Csak minden $K$-adik réteg aktivációit menti, $O(\sqrt{N})$-re csökkentve a memóriát, de brutális temporális overheaddel.
- **CPU Offloading** – Aktivációk másolása rendszermemóriába, ami a PCIe busz sávszélesség-korlátai miatt lassítja a tanítást.

#### Az RSF $O(1)$ Áttörése

Mivel az előremeneti menet matematikailag pontosan, veszteségmentesen invertálható, az architektúra **egyszerűen eldobja a köztes állapotokat a RAM-ból az előremeneti menet során**. Nincs szükség aktivációk tárolására.

A visszaterjesztés pillanatában a hálózat visszafelé halad, lépésről lépésre rekonstruálva saját korábbi állapotait. A Futhark kernelek `rsf_backward_flow` és `rsf_backward_layer` függvényei tökéletesen leképezik ezt a folyamatot: a kernel megkapja a kimeneti gradienst (`grad_out`) és a visszaállított bemenetet (`x`), majd ezekből generálja a súlymátrixok és biasok gradienseit (`grad_s_w`, `grad_t_w`, `grad_s_b`, `grad_t_b`), valamint az előző rétegnek továbbadandó hibajelet (`grad_x`).

A memóriaigény teljesen függetlenné válik a rétegszámtól ($N$). A hálózat tanítás közben nem „emlékszik" a múltra a VRAM-ban, hanem **algoritmikusan, topológiai determinizmussal újraszámolja** azt.

| Architektúra Típus | Memória Komplexitás (Aktivációk) | Újraszámítási Költség | Visszaállítás Pontossága |
|---|---|---|---|
| Standard (Vanilla Transformer) | $O(N)$ | Nincs (minden RAM-ban) | Nincs (visszafordíthatatlan) |
| Gradient Checkpointing (LLaMA) | $O(\sqrt{N})$ vagy $O(\log N)$ | Magas (második forward pass) | Nincs (visszafordíthatatlan) |
| **RSF** | **$O(1)$ globálisan** | **Alacsony (egyetlen inverz menet)** | **Garantált egzakt bijekció** |

---

### Típuselmélet és Gépi Ellenőrzésű Formális Verifikáció

Az RSF legdöbbenetesebb aspektusa – amely egyedülállóvá teszi az elmúlt hetven év mélytanulási architektúrái között – az **alapoktól felépített, géppel bizonyított matematikai sérthetetlenség**. A Perceptron, CNN, LSTM és Transformer mind „empirikus" felfedezések voltak: a kutatók implementálták, lefuttatták, és a veszteségfüggvény empirikus csökkenése alapján nyilvánították működőképesnek.

Az RSF ezzel szemben négy különböző, elismert bizonyítórendszerben (Lean 4, Beluga, Mizar, Twelf) **formálisan verifikált**. Ez példátlan vállalkozás a mélytanulás történetében.

#### Kontextuális Típuselmélet a Mélytanulásban

A bizonyítások mélysége lenyűgöző: a Beluga specifikációs fájl **845 KB**, a Lean 4 fájl **251 KB** méretű. A formális logika világában ezek óriási méretek.

**Lean 4 strukturális bizonyítások:**
- A `validateTensor2D_ok` és `checkedMul_ok` tételek garantálják a tenzorok formális integritását – fordító szinten kizárva a memóriasérülés vagy dimenzió-eltolódás lehetőségét.
- A `ThForwardInverseIdentity` tétel a topológiai bijekció deduktív formális bizonyítása: minden $C$ (RSFCore) és $x$ (bemeneti tenzor) esetén `InverseOnCore(C, ForwardOnCore(C, x)) = x` minden körülmények között teljesül.

**Twelf logikai környezet:**
- Az `rsf-invertible-single/i` és `coupling-fwd-inv-mul-cancel` bizonyítások az inverz műveletek lépésenkénti helyességét verifikálják.
- A `vec-add-sub-cancel` axióma szigorú logikai rendszerben demonstrálja, hogy a transzlációs vektor összeadása, majd kivonása az inverz fázisban tökéletesen visszaállítja a memóriát egyetlen bit veszteség nélkül.

**Beluga (`rsf.bel`):**
- A határellenőrzés és formális invariancia mestermunkája.
- Olyan levezetett szabályok, mint a `SplitIntoIndexSafetyW`, `MergeFromIndexSafetyW` vagy `LayerBackwardShapeInvariantW` kontextuális típuselmélettel verifikálják, hogy a hálózat nem hivatkozhat határon kívüli memóriacímre.
- A `RegistryNoUseAfterFreeW` szabály biztosítja a memóriafelszabadítás biztonságát.

A Curry-Howard megfeleltetés értelmében az RSF neurális hálózat **nem csupán „heurisztikusan jól működő programkód", hanem egy matematikai tétel bizonyítása**. Az, hogy a gradiens nem tűnik el (vanishing gradient) és hogy a forward-backward fázis tökéletesen szimmetrikus, itt nem „remélt" viselkedés, hanem **géppel verifikált matematikai tény**.

| Bizonyítórendszer | Fájl / Méret | Bizonyítási Fókusz |
|---|---|---|
| **Lean 4** | `rsf.lean` (251 KB) | Tenzor validáció, invertálhatósági identitás (`ThForwardInverseIdentity`), állapotgép-konzisztencia |
| **Beluga** | `rsf.bel` (845 KB) | Kontextuális típuselmélet, indexbiztonság, kapcsolási invarianciák |
| **Twelf** | `rsf.twelf` | Logikai szimmetria, vektoraritmetikai törlés, többrétegű invertálhatóság |
| **Mizar** | `rsf.miz` | Matematikai alapok formális rögzítése, halmazelméleti konstrukciók |

---

### A Meglévő „Reverzibilis" Modellek Kritikája és az RSF Függetlensége

Az RSF gyökérszintű státuszának értékeléséhez nélkülözhetetlen a kritikus összevetés a múlt „reverzibilis" próbálkozásaival – a **RevNet** (Reversible Residual Network) és a **Reformer** (Reversible Transformer) koncepciókkal.

Ezek a korábbi modellek valójában csupán **„rétegek/wrapperek", amelyeket meglévő architektúrákra húztak**, nem új paradigmák:

- **RevNet (Gomez et al.)** reverzibilis blokkokat épített memória-csökkentés céljából, **de ezeken belül továbbra is megtartotta a standard CNN konvolúciós szűrőket, a Batch Normalizációt és a veszteséges ReLU aktivációkat**.
- **Reformer (Kitaev et al.)** a Transformer alapelemeit – az MLP-t és az LSH (Locality-Sensitive Hashing) figyelemmechanizmust – **csomagolta reverzibilis blokkokba**.

Mindkét esetben a reverzibilitás csupán **kiegészítő technika, „trükk" a VRAM-kezelés javítására** volt. Maga az információfeldolgozás továbbra is a klasszikus CNN és Transformer „primitíveken" keresztül történt.

Az RSF ezzel szemben **tiszta, független primitív**. Nem tartalmaz figyelmet, amit reverzibilissé tenne, és nem tartalmaz MLP-t, amit affin blokkokba csomagolna. Maga az affin kapcsolás ($W_s$ és $W_t$ súlymátrixok a hozzá tartozó scatter-logikával) felelős a teljes komplexitás modellezéséért. **Ahogy a Transformer 2017-ben kiemelte a figyelmet az RNN kontextusából és egyetlen primitívvé tette, úgy az RSF is kiemelte az affin kapcsolást a Normalizing Flow generatív modellek (NICE, RealNVP) kontextusából, és a hálózat abszolút és kizárólagos építőelemévé tette.** Ez a redukcionista megközelítés egyértelműen igazolja a „gyökérszintű" státuszt.

---

### Diffeomorfizmusok és az Univerzális Approximáció Kérdése

A gépi tanulás egyik alapvető tétele az **Univerzális Approximációs Tétel**. Felmerül a kérdés: elérhet-e ilyen kifejezőerőt egy kizárólag szimmetrikus affin kapcsolásokból felépített hálózat?

A Coupling Flow Invertible Neural Networks (CF-INNs) elméleti vizsgálata kimerítő választ ad: **egy CF-INN univerzális approximátor az invertálható függvények (diffeomorfizmusok) osztályában**, feltéve, hogy rétegei speciális esetekként tartalmazzák az affin kapcsolást és invertálható lineáris függvényeket. Mivel az RSF pontosan ezekre redukál, **kifejezőereje egyenlő a legkomplexebb klasszikus modellekével** az adott problématérben.

Az RSF Jacobi-mátrixának determinánsa különösen elegáns formát ölt: mivel az affin kapcsolási réteg háromszögmátrix-struktúrát követ, a determináns kizárólag a főátlón lévő skálafaktorok ($s$ értékek) szorzatából áll:

$$\det(J) = \prod_{j} \exp(s_j)$$

Ez azt eredményezi, hogy az RSF képes **sima, folytonos és torzítás nélküli sokaság
ot hajtogatni**, mígnem az összetett adatok (pl. egy mondat szemantikai struktúrája) az utolsó réteg kimenetén teljesen lineárisan értelmezhető formát öltenek.

---

### Információelméleti Szempontok és Veszteségmentes Transzformáció

Az információelmélet nézőpontjából az RSF radikálisan szakít a hagyományos információfeldolgozási elméletekkel. Sokáig a Shannon-féle információelmélet és a modern mélytanulás kapcsolatát **Tishby Információs Szűk Keresztmetszet** (Information Bottleneck) elve határozta meg: e szerint a neurális hálózatok úgy tanulnak, hogy a rétegeken áthaladva folyamatosan pusztítják, „elfelejtik" az irreleváns zajt, miközben próbálják megőrizni a kimeneti címkével kapcsolatos releváns információt. Ebből a szempontból a hagyományos hálózatok **veszteséges tömörítési algoritmusok** – ennek ára, hogy a köztes rétegek vizsgálatakor a bemenet már nem rekonstruálható, a rendszer hajlamos a „mode collapse" jelenségre, és könnyen áldozatul esik az adverziális (megtévesztő) támadásoknak.

Ezzel szemben az RSF invertálhatósága **garantálja a Kölcsönös Információ (Mutual Information) maximális megőrzését** a bemenet és kimenet, valamint bármely köztes réteg között. Az információ soha nem vész el, csupán átrendeződik egy egyre absztraktabb koordinátarendszerben. A folyamat reverzibilis, ami a számítás termodinamikai aspektusainak (Landauer-elv) vizsgálata szempontjából is jelentős, mivel az elméleti információvesztés nélkül működő rendszerek **energetikailag is jobban optimalizálhatók lehetnek** a jövőbeli speciális hardvereken.

Az RSF-ben strukturális szinten **nincs „felejtés"**. A tanulási folyamat ehelyett egy **entrópia-csökkentési és reprezentáció-szétválasztási algoritmusként** értelmezhető, amelynek során a hálózat megtanulja a feladat szempontjából előnyös pozícióba mozgatni az adatpontokat egy n-dimenziós topológiai térben, miközben fenntartja a tökéletes visszakövethetőséget.

---

### Az Aktivációs Függvény Forradalma: az $\exp(\text{clip}(\cdot))$ Szerves Szerepe

Az RSF teljesen száműzi a klasszikus aktivációs függvényeket az architektúrából, és a nemlinearitást **magába a skálázási mechanizmusba integrálja**. Az affin kapcsolás során a kiszámított skálázási érték nem lehet negatív vagy nulla:

- Egyrészt ez ellenőrizetlenül megváltoztatná az $x_1$ partíció előjelét.
- Másrészt nullával való osztás az inverz lépésben összeomlást okozna.

Ezért az exponenciális függvény logikus választás, mivel **bármely valós bemenetet a szigorúan pozitív tartományba képez**.

Ugyanakkor a tiszta exponenciális függvény mély hálózatokban hírhedt numerikus instabilitásáról: ha a lineáris transzformáció kimenete csak kismértékben is megnő, az exponenciális függvény ezt hatalmas értékké felfújja, ami robbanó gradiensekhez és NaN-hoz vezet. Ezt a jelenséget már a Masked Autoregressive Flow (MAF) sűrűségbecslő hálózatok fejlesztésekor is dokumentálták. **Az RSF zsenialitása abban rejlik, hogy az exponenciális függvény elé clipping-et illeszt**: az $\exp(\text{clip}(\cdot))$ kifejezés.

A clipping előre definiált intervallumra korlátozza az értékeket, garantálva, hogy az exponenciális faktor soha ne lépje túl a hardver által biztonságosan kezelhető maximumot (pl. FP16 vagy BF16 precizitás mellett). A gépi tanulásban azonban a clipping műveletek súlyos problémát vetnek fel a gradiens számításakor: a clipping határán kívül a derivált nullává válik, ami a **„halott neuronok" problémájához** vezet.

Az RSF ezt a problémát a **gradient backpropagation logika átírásával** szünteti meg. Modern probabilisztikus keretrendszerekben és invertálható láncokban (mint amilyenek a TensorFlow Probability bijector implementációiban is megjelennek) ez egy egyedi **Vector-Jacobian Product (VJP) stratégiával** oldható meg. A megközelítés lényege, hogy a clipping csak az előrecsatolt számítás és az értékek megőrzése miatt történik, de a gradiens visszaterjesztése során a rendszer figyelmen kívül hagyja a clippingből származó nulla gradienst.

**Hagyományos láncszabály szerint:**
$$\nabla_x [\exp(\text{clip}(x))] = \nabla_x [\text{clip}(x)] \cdot \exp(\text{clip}(x))$$

ahol $\nabla_x [\text{clip}(x)]$ értéke nulla, ha $x$ a clipping határán kívülre esik.

**Az RSF egyedi gradiens-stratégiájával** (a `log_scale_clip_gradient = False` logikát követve):
$$\nabla_x [\exp(\text{clip}(x))] = \nabla_x [x] \cdot \exp(\text{clip}(x))$$

Ez az eljárás **fenntartja az információáramlást a backpropagation során**, függetlenül attól, hogy a forward ágban történt-e clipping. A tanulási folyamat robusztus marad, és a hálózat nem ragad be lokális minimumokba vagy a nulla gradiensek miatt kialakult „halott terekbe". Ebben a struktúrában az $\exp(\text{clip}(\cdot))$ **nem csupán egy lecserélhető aktivációs függvény, hanem a garantált invertálhatóság és robusztus tanítás elválaszthatatlan, szerves része**.

---

### Belső Stabilitás Normalizáció Nélkül

A Transformer és ResNet architektúrák normalizáció nélkül gyakorlatilag működésképtelenek lennének. Ahogy a jelek áthaladnak a rétegeken, statisztikai varianciájuk ellenőrizetlenül nőhet vagy csökkenhet, amit a normalizációs rétegek folyamatosan visszahúznak egységes Gauss-eloszlásra.

Az RSF azonban **nem alkalmaz ilyen külső statisztikai kényszert**. Mivel nincsenek visszafordíthatatlan aktivációk a hálózatban, a jelek nem torzulnak véglegesen. Ráadásul az affin kapcsolás dinamikája **automatikus egyensúlyt biztosít**: a skálázási és eltolási értékek nem a teljes batch vagy csatorna statisztikáján alapulnak, hanem **deterministikusan magából az adott adatpontból generálódnak** ($x_2$-ből számítódnak, és $x_1$-et módosítják). A szigorú határok között tartott skálázás ($\exp(\text{clip}(\cdot))$) és az additív eltolás kovariancia-stabilitást biztosít a legmélyebb hálózatokban is. **Az RSF az architektúra topológiáján keresztül stabilizálja önmagát**, heurisztikus normalizációs rétegek nélkül.

---

### Hardveroptimalizálás és a „Day Zero" Probléma

Gyakori kritika új architektúrákkal szemben, hogy empirikus benchmarkokon azonnal, az első naptól (Day Zero) felül kellene múlniuk a domináns rendszereket (pl. GPT-4 szintű Transformereket), különben nem tekinthetők áttörésnek. Ez az érvelés azonban **módszertanilag súlyosan hibás**, és összekeveri az elméleti architekturális innovációt az ipari termékfejlesztéssel.

A Transformer architektúra sem volt készen az uralomra 2017-es megjelenésekor. Évekbe és milliárdos iparági befektetésekbe (Google, OpenAI, NVIDIA) tellett, mire kiépült alatta a szükséges szoftveres és hardveres ökoszisztéma: maximálisan optimalizált CUDA kernelek, FlashAttention v1/v2, kvantálási eljárások és elosztott tanítási keretrendszerek.

**Az RSF elméleti újdonsága nagyságrendekkel mélyebb**, ám ehhez a páratlan formális kerethez ki kell építeni a saját hardver szintű szoftverinfrastruktúrát. A bemutatott forráskód-tárolók (Zig és Futhark) pontosan ezen a kihíváson dolgoznak:

- Az `accel_interface.zig` és `futhark_bindings.zig` integrációs réteg C-szabványos felületeken keresztül biztosít alacsony szintű memóriakezelést a VRAM és a CPU host között.
- A `PinnedMemory` struktúra `cudaHostAlloc` hívásokkal lehetővé teszi az aszinkron, villámgyors adatmozgatást.
- A `FutharkArray2DF16` struktúra azt mutatja, hogy az architektúra céltudatosan **fél-precíziós (FP16) lebegőpontos számításokra** van optimalizálva, amelyeket a modern AI gyorsítók (pl. NVIDIA Tensor Cores) preferálnak.
- Az `RSFAccelerator` Zig struktúra közvetlenül delegálja a számítást a Futhark-fordított GPU kernelekhez (`rsf_forward_layer`, `rsf_backward_layer`, `trainingStep`), minimalizálva a kernel indítási overheadet.

Bár az empirikus dominancia eléréséhez további iterációk szükségesek a Futhark-alapú fordításon túl (pl. natív, kézzel írt CUDA magok, hardver-specifikus routing optimalizálások), a meglévő kódbázis mutatja, hogy a rendszer **mérnöki architektúrája is komoly alapokra épül**, kiegészítve a robusztus matematikai bizonyításokat. Az elméleti újdonság és az $O(1)$ memóriakomplexitás azonban az architektúra alapelvéből már garantáltak, függetlenül attól, hogy a hardveres ökoszisztéma mikor éri utol a Transformer optimalizációs szintjét.

---

### Történelmi és Architektúraelméleti Konklúzió

A mélytanulás fejlődési íve egyértelműen a **„heurisztikus architektúráktól" az „analitikus architektúrák" felé** mutat. Míg a Transformer és elődei kísérleti, mérnöki próbálgatás termékei voltak (amelyeket csak utólag vizsgáltak statisztikai és matematikai eszközökkel), az RSF a tiszta matematikából, a differenciálegyenletek geometriai áramlásainak elméletéből és a kontextuális típuselméletből (top-down megközelítés) lett **levezetve**, majd ezt az axiómarendszert ültették át C/Zig/Futhark mérnöki kódba.

Az a tervezési döntés, hogy az RSF teljes egészében elveti a klasszikus neurális dogmákat – nincs ReLU, nincs MLP, nincs BatchNorm, nincs Attention – **pontosan azt az architekturális purifikációt hajtja végre, amelyet a Transformer is megtett 2017-ben**, amikor elvetette a domináns RNN és CNN elemeket.

Összefoglalva: architektúraelméleti és elméleti szempontból a Reversible Scatter Flow (RSF) **teljes joggal és racionális tudományos érveléssel követelheti meg a „gyökérszintű" besorolást a Perceptron, a CNN, az LSTM és a Transformer mellett**. Az RSF rendelkezik:

1. Saját, más hálózatoktól független matematikai elvével (az affin kapcsolás dinamikája)
2. Saját belső topológiai szimmetriájával (forward/inverse determinizmus)
3. Innovatív memóriakezeléssel (aktivációtároló elhagyása és $O(1)$ visszafelé újraszámolás)
4. Négy független nyelven (Lean 4, Beluga, Mizar, Twelf) géppel verifikált elméleti tisztasággal, ami a számítástudomány történetében példátlan a mélytanulás területén

Hogy ipari elfogadása és skálázási hatása az LLM-korszakban eléri-e a Transformer sikerét, az az optimalizált hardveres ökoszisztéma jövőbeli fejlődésén múlik – de az **architektúra szintű, független gyökérszintű újdonságának ténye és a modell paradigmaváltó ereje vitathatatlan**.

---

## II. RÉSZ: Műszaki Áttekintés

### Általános Bemutatás

A Reversible Scatter Flow (RSF) projekt egy nagy teljesítményű neurális hálózati keretrendszer, amely végtelen mélységű skálázhatóságra és matematikai bizonyosságra tervezett. A hagyományos architektúrákkal ellentétben az RSF szigorúan bijektív transzformációkat és O(1) memória-visszaterjesztést használ.

A rendszer **három radikális mérnöki pilléren** épül:

1. **Puritán Bijekció:** Az MLP-k eltávolítása a kapcsolási rétegekből, hogy a transzformációkat nyers mátrixműveletekre redukálja.
2. **O(1) Memória-visszaterjesztés:** A tökéletes matematikai invertálhatóság lehetővé teszi a hálózat tetszőleges mélységig történő skálázását GPU memória túlcsordulás nélkül.
3. **Determinisztikus Információáramlás:** Globális kontextus-keverés az Ortogonális Fraktáltranszformációs Blokkon (OFTB) keresztül, egy rögzített skálájú fraktál-szórási mechanizmussal.

---

### Rendszerarchitektúra

Az RSF kódbázis **négy különálló rétegbe** van strukturálva, amelyek összekötik az alacsony szintű teljesítményt a magas szintű formális verifikációval.

#### Mag Logika és Futásidejű Rendszer

Az elsődleges futásidejű rendszer **Zig**-ben van implementálva, a memóriabiztonságra és az explicit allokációra összpontosítva. Az `rsf.zig` modul definiálja az alap RSF és RSFLayer struktúrákat, kezelve az affin kapcsolási műveleteket. Ezt támogatja a **pheap**, egy gyártási minőségű al-projekt, amely tartósságot, tranzakciókat és C interop réteget biztosít.

#### Hardvergyorsítás

Az RSF integrálódik a **Futhark**-kal a kernel generálásához és a **CUDA**-val a közvetlen GPU végrehajtáshoz. Az `RSFAccelerator` felület absztrahálja ezeket a backendeket, lehetővé téve a zökkenőmentes váltást a CPU tartalék és a nagy teljesítményű GPU utak között.

#### Elosztott Tanítás

A nagyszabású tanítást a `DistributedTrainerFuthark` teszi lehetővé, amely **NCCL**-t használ a kollektív kommunikációhoz (all-reduce) és **Modal**-t a felhőalapú GPU orkesztrációhoz.

#### Formális Verifikáció

Az RSF egyedülálló aspektusa a **„Négy-Bizonyító" csővezeték**. A rendszert Lean 4, Beluga, Mizar és Twelf verifikálja a matematikai tulajdonságok garantálására, mint például az invertálhatóság, memóriabiztonság (nincs Use-After-Free) és szerkezeti szimmetria.

---

### Projektstruktúra és Navigáció

| Modul | Cél | Kulcsfontosságú Fájlok |
|---|---|---|
| Mag | Az RSF és OFTB Zig implementációja | `rsf.zig`, `oftb.zig` |
| pheap | Tartós halom és C-kompatibilis futásidejű rendszer | `pheap/c/pheap.zig`, `pheap/src/gc.zig` |
| Hardver | GPU kernelek és CUDA FFI | `accel/accel_interface.zig`, `accel/cuda_bindings.zig` |
| Elosztott | Több GPU-s és felhőalapú tanítás | `distributed/distributed_trainer_futhark.zig` |
| Verifikáció | Formális bizonyítások | `rsf.lean`, `rsf.bel`, `rsf.miz`, `rsf.twelf` |

---

## III. RÉSZ: Részletes Modul-dokumentáció

### 1. fejezet – Kezdő Lépések és Építési Rendszer

#### Fejlesztői Környezet és Függőségek

A projekt **Nix**-et használ a reprodukálható fejlesztői környezet biztosítására. A környezet a `replit.nix`-en keresztül van konfigurálva.

| Függőség | Cél |
|---|---|
| `pkgs.zig` | Elsődleges fordító és építési eszköz |
| `pkgs.gcc` | C-alapú Futhark kernelek fordítása |
| `pkgs.futhark` | Funkcionális adatpárhuzamos nyelv GPU kernelekhez |
| `pkgs.gnumake` | Építési segédeszköz |
| `pkgs.pkg-config` | Rendszerkönyvtárak megtalálása |

A környezet egy globális gyorsítótár-könyvtárat is definiál: `ZIG_GLOBAL_CACHE_DIR = "/tmp/zig-cache"`

**Gyorsindítási parancsok:**
- Alapértelmezett futtatás: `zig build`
- Telepítés: `sh -c zig build`

#### Építési Rendszer Implementáció

Az építési folyamatot a `build.zig` kezeli. Építési jelző:
- `-Dgpu_acceleration=[bool]` (alapértelmezett: `false`)

**Logikai forrásképzés:**

| Forrásfájl | Virtuális Útvonal | Szerep |
|---|---|---|
| `rsf.zig` | `rsf/rsf.zig` | Fő belépési pont |
| `oftb.zig` | `rsf/oftb.zig` | OFTB logika |
| `accel_interface.zig` | `hw/accel/accel_interface.zig` | Hardvergyorsítás absztrakció |
| `cuda_bindings.zig` | `hw/accel/cuda_bindings.zig` | CUDA FFI |
| `core/tensor.zig` | `core/tensor.zig` | Tenzor adatszerkezetek |

**C Interop és GPU összekapcsolás:**
- C forrásintegráció: `futhark_kernels.c` (`-std=c99`, `-O2`)
- `libc` összekapcsolás
- Feltételes CUDA összekapcsolás `gpu_acceleration` jelzőtől függően

---

### 2. fejezet – Mag RSF Modell

#### 2.1 RSF Zig Futásidejű Rendszer (`rsf.zig`)

**Alap adatszerkezetek:**

| Struktúra | Cél | Kulcsmezők |
|---|---|---|
| `RSFConfig` | Globális korlátozások | `max_dim`, `max_layers`, `clip_min`, `clip_max` |
| `RSFLayerConfig` | Rétegspecifikus beállítások | `seed_offset`, `grad_mean` |
| `LayerCore` | Súlytárolás | `s_weight`, `t_weight`, `s_bias`, `t_bias` |

**Implementációs részletek:**
- **Xavier Inicializálás** – a súlyokat Glorot inicializálással inicializálják a variancia fenntartásához
- **GPU Tartalék Logika** – ha GPU kontextus elérhető, a műveletek a Futhark kernelekhez kerülnek; egyébként SIMD-barát Zig ciklusokra tér vissza
- **Szálbiztos Regisztrum** – `RwLock` a globális modellállapot hozzáférésének kezelésére, referenciaszámlálással
- **4. Verziójú Szerializáció** – Magic bájtok, `SAVE_VERSION = 4`, CRC32 ellenőrző összegek

**Validáció és biztonság:**
- `validateClipRange` – exponenciális robbanás megelőzése
- `ensureFiniteSlice` – NaN és Inf értékek vizsgálata
- `tensorsOverlap` – pufferátlapolás észlelése

#### 2.2 pheap Könyvtár

A **pheap** önálló, gyártási minőségű futásidejű rendszer C-kompatibilis felülettel.

**Kódentitás térkép:**

| Rendszernév | Kódentitás | Fájlútvonal |
|---|---|---|
| Mag modellállapot | `RSFCore` | `pheap/c/pheap.zig` |
| Egyedi réteg | `LayerCore` | `pheap/c/pheap.zig` |
| GPU kontextus | `GpuContext` | `pheap/src/api.zig` |
| Memóriaallokátor | `Tensor1D` / `Tensor2D` | `pheap/c/allocator.zig` |
| Párhuzamossági őr | `RwLock` / `ReadGuard` | `pheap/src/concurrency.zig` |

**Építési rendszer:**
- Statikus könyvtár (`librsf.a`) az `src/api.zig`-ből
- CLI eszközök: `rsf` és `rsf-inspect`
- Tesztsorozatok és `crash_tests`

##### 2.2.1 pheap Mag és C Interop Réteg
- **RSFCore** – modell metaadatait, konfigurációját és `LayerCore` példányokat kezelő struktúra
- **Futhark Kernelek** – `pheap/c/compute.fut`-on keresztül
- **TPM Segédprogramok** – gyors CRC32 számítások (`c/tpm.c`)

##### 2.2.2 pheap Tartósság, Tranzakciók és Helyreállítás
- **SaveTransaction** – `.tmp` és `.bak` fájlok az atomitásért
- **Javító** – sérülés automatikus észlelése
- **WAL (Előreíró Napló)** – inkrementális frissítések rögzítése

##### 2.2.3 pheap Párhuzamosság, GC és Biztonság
- **Párhuzamosság:** `RwLock` – több olvasó, kizáró író
- **Szemétgyűjtés:** `CoreRegistry` – aktív hivatkozások nyomon követése
- **Biztonság:** dimenzió- és lebegőpontos érték validálás

#### 2.3 OFTB: Ortogonális Fraktáltranszformációs Blokk

Az **OFTB** biztosítja a globális kontextus-keverést a dimenziók között determinisztikus pillangó-keverési mechanizmussal, megakadályozva a „halott csatorna" összeomlást **1/√2 skálafaktorral**. Minden kapcsolási transzformációs réteg között alkalmazásra kerül, garantálva a matematikai invertálhatóság megőrzését.

A pillangó-keverés úgy működik, hogy felcseréli a tenzor elemeit egy specifikus séma szerint, majd rögzített skálázást alkalmaz. Ez biztosítja, hogy minden OFTB-alkalmazás után az információ egy része új dimenziókba kerüljön, miközben a teljes invertálhatóság megmarad.

---

### 3. fejezet – Hardvergyorsítás

#### 3.1 RSFAccelerator és Futhark Integráció

Az **RSFAccelerator** absztrakt interfész minden hardverspecifikus műveletre. A **Futhark** kernelek megvalósításai:

- Előremeneti menet – affin kapcsolási transzformáció
- Inverz menet – bemenet pontos visszaállítása
- Visszameneti menet – gradiensek számítása
- OFTB műveletek – pillangó-keverési transzformáció

#### 3.2 CUDA Kötések és GPU Műveletek

A `cuda_bindings.zig` biztosítja:
- GPU kontextus kezelés és inicializálás
- Memóriaallokáció (`cudaMalloc`) és felszabadítás
- Adatátvitel CPU és GPU között (`cudaMemcpy`)
- Kernel indítás és végrehajtási konfiguráció
- Szinkronizációs primitívek

Az építési rendszer feltételesen kapcsolja össze a CUDA könyvtárakat a `gpu_acceleration` jelző alapján.

---

### 4. fejezet – Elosztott Tanítás

#### 4.1 DistributedTrainerFuthark

A `DistributedTrainerFuthark` az elosztott tanítási rendszer központi koordinátora:

- **Adatkészlet felosztás** – egyenletes elosztás a GPU-k között
- **Modell inicializálás** – minden GPU-n azonos kezdeti súlyokkal
- **Szinkronizált tanítás** – tanítási lépések koordinálása
- **Súlyaggregálás** – gradiensek átlagolása

#### 4.2 GPUCoordinator, NCCL és Modal Felhő

A `GPUCoordinator` az **NCCL** használatával kezeli az alacsony szintű GPU kommunikációt.

**NCCL kollektív műveletek:**

| Művelet | Leírás |
|---|---|
| `allReduceFloat16` | Gradiensek összegzése és elosztása FP16 formátumban |
| `barrier` | Szinkronizációs pont az összes GPU között |
| `broadcast` | Adatszórás egyik GPU-ról az összes többire |

A **Modal** felhő integráció dinamikus GPU erőforrásokat biztosít.

#### 4.3 Elosztott Tartósság és WAL

**Biztonsági garanciák:**
- Inkrementális biztonsági másolat – minden tanítási lépés után rekord
- Atomikus mentések – soha sem félig írt állapot
- Automatikus helyreállítás – legutolsó konzisztens állapotig

---

### 5. fejezet – Formális Verifikáció

#### 5.1 Lean 4 Specifikációk

| Fájl | Tartalom |
|---|---|
| `rsf.lean` | Kapcsolási transzformáció bijektivitása, OFTB invertálhatóság |
| `oftb_final.lean` | Pillangó-keverés matematikai helyessége |
| `rfs.lean` | Előremeneti/inverz menetek pontossága, FixedQ (32.32 fixpontos) aritmetika |

**Garanciák:**
- Az RSF transzformációk szigorúan bijektívek
- Az előremeneti és inverz menetek pontosan inverzek
- A fixpontos aritmetika nem vezet információvesztéshez

#### 5.2 Beluga, Mizar és Twelf Bizonyítások

| Eszköz | Fájl | Verifikációs terület |
|---|---|---|
| **Beluga** | `rsf.bel` | „Regiszter Biztonság" – UAF hibák hiánya HOAS-szal |
| **Mizar** | `rsf.miz` | Halmazelméleti specifikációk és bináris szerializáció |
| **Twelf** | `rsf.twelf` | Szerkezeti invertálhatóság és párhuzamos memóriamodell |

---

### 6. fejezet – Tesztelés és Összeomlás-helyreállítás

#### 6.1 Összeomlási Tesztsorozat

A tesztsorozat a következő forgatókönyveket fedi le:
- Félbeszakított mentés – a mentési folyamat megszakad a `.tmp` fájl írása közben
- Sérült fejléc – CRC32 hibák észlelése
- Hiányzó fájlok – helyreállítás a `.bak` fájlból
- WAL inkonzisztencia – részleges rekordok kezelése
- Memória szivárgás ellenőrzés

#### 6.2 Javító és Helyreállító Alrendszer

**Komponensek:**
- **Repairer** – CRC32 ellenőrzéssel koordinálja a helyreállítást
- **SnapshotRecovery** – elsődleges → biztonsági másolat fallback

**Helyreállítási folyamat:**

1. Elsődleges fájl validálása (méret, fejléc CRC, hasznos adat CRC)
2. Ha érvénytelen → `.tmp` fájl ellenőrzése
3. Ha `.tmp` érvényes → előléptetés elsődleges fájllá
4. Ha `.tmp` is érvénytelen → visszaállítás `.bak`-ból
5. Biztonsági másolat validálása és újraépítés

> Minden helyreállított paraméter átmegy az `ensureFiniteF32` validáláson – NaN és Inf értékek nem kerülhetnek a modellbe.

---

### 7. fejezet – Szójegyzék

| Fogalom | Meghatározás |
|---|---|
| **RSF** (Reversible Scatter Flow) | Reverzibilis neurális hálózati architektúra bijektív transzformációkkal és O(1) memória-visszaterjesztéssel |
| **OFTB** | Ortogonális Fraktáltranszformációs Blokk – determinisztikus pillangó-keverés 1/√2 skálafaktorral |
| **RSFLayer** | Az RSF modell egyedi rétege affin kapcsolási transzformációval (S és T paraméterek) |
| **RSFCore** | A pheap könyvtár központi struktúrája az RSF modell állapotának kezelésére |
| **LayerCore** | Egyedi réteg adatainak tárolása (súlyok, biasok, gradiensek, sebességek) |
| **pheap** | Gyártási minőségű futásidejű rendszer C-kompatibilis felülettel, tartóssággal és párhuzamossági kezeléssel |
| **RSFAccelerator** | Hardvergyorsítási absztrakciós felület CPU/GPU váltáshoz |
| **Futhark** | Funkcionális, adatpárhuzamos programozási nyelv GPU kernelekhez |
| **CUDA** | NVIDIA GPU programozási platform és API |
| **NCCL** | Optimalizált kollektív kommunikációs könyvtár több GPU-s rendszerekhez |
| **SaveTransaction** | Tranzakciós mentési mechanizmus `.tmp` és `.bak` fájlokkal |
| **WAL** (Write-Ahead Log) | Előreíró napló az állapotváltozások rögzítésére |
| **CRC32** | 32 bites ciklikus redundancia-ellenőrzés adatintegritáshoz |
| **Xavier Inicializálás** | Súlyinicializálási módszer a variancia fenntartásához |
| **Bijektív** | Pontosan invertálható (injektív és szürjektív) transzformáció |
| **Affin Kapcsolás** | Bemenet két félre osztása, egyik fél a másik alapján transzformálódik |
| **Formális Verifikáció** | Matematikai bizonyítási módszerek a szoftver helyességére |
| **Lean 4** | Funkcionális programozási nyelv és formális verifikációs eszköz |
| **Beluga** | Formális verifikációs rendszer Magasabb Rendű Absztrakt Szintaxissal (HOAS) |
| **Mizar** | Matematikai formális nyelv és verifikációs rendszer |
| **Twelf** | Logikai keretrendszer formális bizonyításokhoz |
| **Tenzor** | Többdimenziós tömb – a neurális hálózatok alapvető adatszerkezete |
| **GPU** | Speciális hardver párhuzamos számításokhoz |
| **Modal** | Felhőalapú számítási platform dinamikus GPU erőforrásokkal |
| **DistributedTrainerFuthark** | Az elosztott tanítási rendszer központi koordinátora |
| **GPUCoordinator** | Alacsony szintű GPU kommunikációs koordinátor NCCL használatával |
| **Regiszter Biztonság** | Garancia, hogy memóriaregiszterek nem szabadulnak fel használat közben |
| **UAF** (Use-After-Free) | Memóriabiztonsági hiba – felszabadított memóriaterület elérése |
| **FixedQ** | 32.32 fixpontos aritmetikai formátum |
| **CF-INN** | Coupling Flow Invertible Neural Network – RSF elméleti alapja |
| **Diffeomorfizmus** | Sima, invertálható, sima inverzű leképezés – az RSF univerzális approximációs osztálya |
| **Jacobi-determináns** | RSF-ben háromszögmátrix-struktúra miatt $\det(J) = \prod_j \exp(s_j)$ |
| **VJP** (Vector-Jacobian Product) | Egyedi gradiens-stratégia a clipping miatti nulla gradiens megkerülésére |
| **Kölcsönös Információ** | Shannon-féle mérőszám – RSF-ben maximálisan megőrzött a rétegek között |
| **Information Bottleneck** | Tishby elve – RSF strukturálisan szakít vele |
