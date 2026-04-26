# Reversible Scatter Flow (RSF) – Dokumentáció

---

## Áttekintés

A Reversible Scatter Flow (RSF) projekt egy nagy teljesítményű neurális hálózati keretrendszer, amely végtelen mélységű skálázhatóságra és matematikai bizonyosságra tervezett. A hagyományos architektúrákkal ellentétben az RSF szigorúan bijektív transzformációkat és O(1) memória-visszaterjesztést használ, megszüntetve az aktivációk tárolásának szükségességét az előremeneti menet során.

A rendszer három radikális mérnöki pilléren épül:

1. **Puritaán Bijekció:** Az MLP-k eltávolítása a kapcsolási rétegekből, hogy a transzformációkat nyers mátrixműveletekre redukálja
2. **O(1) Memória-visszterjesztés:** A tökéletes matematikai invertálhatóság lehetővé teszi a hálózat számára, hogy tetszőleges mélységig skálázódjon GPU memória túlcsordulás nélkül
3. **Determinisztikus Információáramlás:** Globális kontextus-keverés az Ortogonális Fraktáltranszformációs Blokkon (OFTB) keresztül, egy rögzített skálájú fraktál-szórási mechanizmus

---

## Rendszerarchitektúra

Az RSF kódbázis négy különálló rétegbe van strukturálva, amelyek összekötik az alacsony szintű teljesítményt a magas szintű formális verifikációval.

### Mag Logika és Futásidejű Rendszer

Az elsődleges futásidejű rendszer Zig-ben van implementálva, a memóriabiztonságra és az explicit allokációra összpontosítva. Az `rsf.zig` modul definiálja az alap RSF és RSFLayer struktúrákat, kezelve az affin kapcsolási műveleteket. Ezt támogatja a **pheap**, egy gyártási minőségű al-projekt, amely tartósságot, tranzakciókat és C interop réteget biztosít.

### Hardvergyorsítás

A nehéz számítási terhek kezeléséhez az RSF integrálódik a **Futhark**-kal a kernel generáláshoz és a **CUDA**-val a közvetlen GPU végrehajtáshoz. Az RSFAccelerator felület absztrahálja ezeket a backendeket, lehetővé téve a zökkenőmentes váltást a CPU tartalék és a nagy teljesítményű GPU utak között.

### Elosztott Tanítás

A nagyszabású tanítást a `DistributedTrainerFuthark` teszi lehetővé, amely NCCL-t használ a kollektív kommunikációhoz (all-reduce) és Modal-t a felhőalapú GPU orkesztrációhoz.

### Formális Verifikáció

Az RSF egyedülálló aspektusa a **„Négy-Bizonyító" csővezeték**. A rendszert Lean 4, Beluga, Mizar és Twelf verifikálja a matematikai tulajdonságok garantálására, mint például az invertálhatóság, memóriabiztonság (nincs Használat-Szabadítás-Után) és szerkezeti szimmetria.

---

## Projektstruktúra és Navigáció

| Modul | Cél | Kulcsfontosságú Fájlok |
|---|---|---|
| Mag | Az RSF és OFTB Zig implementációja | `rsf.zig`, `oftb.zig` |
| pheap | Tartós halom és C-kompatibilis futásidejű rendszer | `pheap/c/pheap.zig`, `pheap/src/gc.zig` |
| Hardver | GPU kernelek és CUDA FFI | `accel/accel_interface.zig`, `accel/cuda_bindings.zig` |
| Elosztott | Több GPU-s és felhőalapú tanítás | `distributed/distributed_trainer_futhark.zig` |
| Verifikáció | Formális bizonyítások (Lean, Beluga stb.) | `rsf.lean`, `rsf.bel`, `rsf.miz` |

---

## 1. fejezet – Kezdő Lépések és Építési Rendszer

Ez a fejezet a fejlesztői környezet beállítását, a Nix-alapú függőségkezelést és az Zig építési rendszer konfigurációját ismerteti.

### Fejlesztői Környezet és Függőségek

A projekt **Nix**-et használ a reprodukálható fejlesztői környezet biztosítására különböző gépek között. A környezet a `replit.nix`-en keresztül van konfigurálva.

| Függőség | Cél |
|---|---|
| `pkgs.zig` | Elsődleges fordító és építési eszköz az RSF futásidejű rendszerhez |
| `pkgs.gcc` | Szükséges a C-alapú Futhark kernelek fordításához és összekapcsolásához |
| `pkgs.futhark` | Nagy teljesítményű funkcionális adatpárhuzamos nyelv GPU kernelekhez |
| `pkgs.gnumake` | Építési segédeszköz kiegészítő feladatokhoz |
| `pkgs.pkg-config` | Segédprogram a rendszerkönyvtárak megtalálásához az építési folyamat során |

A környezet egy globális gyorsítótár-könyvtárat is definiál a Zig számára a jogosultsági problémák megelőzésére:
```
ZIG_GLOBAL_CACHE_DIR = "/tmp/zig-cache"
```

### Gyorsindítási Parancsok

- **Alapértelmezett futtatási parancs:** `zig build`
- **Telepítési parancs:** `sh -c zig build`

### Építési Rendszer Implementáció

Az építési folyamatot a `build.zig` kezeli, amely kihasználja az Zig Építési Rendszer API-t a C interop, GPU gyorsítás jelzők és belső modulképzés kezelésére.

**Építési jelző:**
- `-Dgpu_acceleration=[bool]` (alapértelmezett: `false`) – Ez a jelző az Zig kódba kerül az `addOptions`-en keresztül, lehetővé téve a futásidejű rendszer számára a GPU-specifikus logika váltását.

### Logikai Forrásképzési Táblázat

| Forrásfájl | Virtuális Útvonal | Szerep |
|---|---|---|
| `rsf.zig` | `rsf/rsf.zig` | Fő belépési pont az RSF könyvtárhoz |
| `oftb.zig` | `rsf/oftb.zig` | Ortogonális Fraktáltranszformációs Blokk logika |
| `accel_interface.zig` | `hw/accel/accel_interface.zig` | Hardvergyorsítás absztrakció |
| `cuda_bindings.zig` | `hw/accel/cuda_bindings.zig` | FFI a CUDA meghajtó API-hoz |
| `core/tensor.zig` | `core/tensor.zig` | Alapvető tenzor adatszerkezetek |

### C Interop és GPU Összekapcsolás

Az RSF könyvtár `rsf` névvel ellátott statikus könyvtárként kerül fordításra. Az építési rendszer a következőket végzi:

- **C forrásintegráció:** A `futhark_kernels.c` hozzáadása specifikus jelzőkkel (`-std=c99`, `-O2`)
- **Szabványos könyvtár összekapcsolás:** Az `libc`-hez való kapcsolás a C-alapú kernelek támogatásához
- **Feltételes CUDA összekapcsolás:** Ha a `gpu_acceleration` engedélyezett, az építő a `cuda` könyvtárát kapcsolja össze

---

## 2. fejezet – Architektúra Áttekintés

### Négyrétegű Szerkezeti Modell

| Réteg | Leírás |
|---|---|
| **Formális Verifikációs Réteg** | Lean 4, Beluga, Mizar és Twelf – matematikai garanciák az invertálhatóságról, memóriabiztonságról és szerkezeti integritásról |
| **Zig Futásidejű Réteg** (`rsf.zig` / `pheap`) | Az alap végrehajtási motor – RSF és RSFLayer struktúrák, affin kapcsolási transzformációk, életciklus-kezelés |
| **GPU Gyorsítási Réteg** (`accel/`) | Nagy teljesítményű implementációk Futhark-generált kernelek és CUDA kötések használatával |
| **Elosztott Tanítási Réteg** (`distributed/`) | Több GPU-s munkaterhelések orkesztrálása NCCL-lel és osztott adatkészlet-betöltéssel |

---

## 2.1 – RSF Zig Futásidejű Rendszer (`rsf.zig`)

Az `rsf.zig` fájl az elsődleges CPU-oldali futásidejű rendszer. Definiálja az alap adatszerkezeteket, matematikai transzformációkat és életciklus-kezelést.

### Alap Adatszerkezetek

| Struktúra | Cél | Kulcsmezők |
|---|---|---|
| `RSFConfig` | Globális korlátozások | `max_dim`, `max_layers`, `clip_min`, `clip_max` |
| `RSFLayerConfig` | Rétegspecifikus beállítások | `seed_offset`, `grad_mean` |
| `LayerCore` | Súlytárolás | `s_weight`, `t_weight`, `s_bias`, `t_bias` |

### Kapcsolási Transzformáció Matematika

**Előremeneti menet** – egy `[x1, x2]`-re osztott bemenet esetén:

1. **Osztás:** A bemenet `x` → `x1` és `x2`
2. **Skála és Transzláció:** `S = affine(x1, W_s, b_s)` és `T = affine(x1, W_t, b_t)`
3. **Transzformáció:** `y1 = x1` és `y2 = x2 * exp(S) + T`

**Inverz menet** – a bemenet pontos visszaállítása:

1. `x1 = y1`
2. `x2 = (y2 - T) * exp(-S)`

### Implementációs Részletek

**Xavier Inicializálás**
A súlyokat Xavier (Glorot) inicializálással inicializálják a variancia fenntartásához a rétegek között. A futásidejű rendszer kiszámítja a határértéket a bemeneti/kimeneti dimenziók alapján, és ennek megfelelően tölti fel az `s_weight` és `t_weight` tenzorokat.

**GPU Tartalék Logika**
Az `rsf.zig` logikát tartalmaz a hardvergyorsítás elérhetőségének ellenőrzésére. Ha GPU kontextus elérhető, a műveletek a Futhark kernelekhez kerülnek; egyébként a futásidejű rendszer SIMD-barát Zig ciklusokra tér vissza.

**Szálbiztos Regisztrum**
- `RwLock` – a globális modellállapot hozzáférésének kezelésére
- **Referenciaszámlálás** – biztosítja, hogy a rétegek ne kerüljenek felszabadításra, amíg menet folyamatban van

**4. Verziójú Szerializáció**
- **Magic bájtok** – azonosítja az RSF fájlformátumot
- `SAVE_VERSION = 4`
- **CRC32** – minden szerializált blokk ellenőrző összeggel védett

**Validáció és Biztonság**
- `validateClipRange` – biztosítja, hogy az S és T értékek ne vezessenek exponenciális robbanáshoz
- `ensureFiniteSlice` – a tenzorokat NaN vagy Inf értékekre vizsgálja
- `tensorsOverlap` – puffer-aliasszágot észlel a memóriasérülés megelőzésére

---

## 2.2 – pheap Könyvtár

A **pheap** könyvtár egy önálló, gyártási minőségű futásidejű rendszer az RSF modellhez. C-kompatibilis felületet, robusztus tartóssági mechanizmusokat és szálbiztos végrehajtást biztosít.

### Kódentitás Térkép

| Rendszernév | Kódentitás | Fájlútvonal |
|---|---|---|
| Mag Modell Állapot | `RSFCore` | `pheap/c/pheap.zig` |
| Egyedi Réteg | `LayerCore` | `pheap/c/pheap.zig` |
| GPU Kontextus | `GpuContext` | `pheap/src/api.zig` |
| Memóriaallokátor | `Tensor1D` / `Tensor2D` | `pheap/c/allocator.zig` |
| Párhuzamossági Őr | `RwLock` / `ReadGuard` | `pheap/src/concurrency.zig` |

### Építési Rendszer

- **Statikus könyvtár** (`librsf.a`) – az `src/api.zig`-ből fordítva
- **CLI eszközök:** `rsf` (általános műveletek) és `rsf-inspect` (pillanatkép hibakeresés)
- **Tesztsorozatok:** egységtesztek és `crash_tests` a helyreállítási logika ellenőrzésére

---

## 2.2.1 – pheap Mag és C Interop Réteg

- **RSFCore** – a modell metaadatait, konfigurációját és a `LayerCore` példányok tömbjét kezelő központi struktúra
- **Futhark Kernelek** – nagy teljesítményű számítási kernelek az előremeneti, inverz és visszameneti menetekhez (`pheap/c/compute.fut`)
- **TPM Segédprogramok** – alacsony szintű C függvények gyors CRC32 számításokhoz és cache-kezeléshez (`c/tpm.c`)

---

## 2.2.2 – pheap Tartósság, Tranzakciók és Helyreállítás

A pheap egy szigorú tartóssági vermet implementál, amelyet rendszerösszeomlások és hardverhibák túlélésére terveztek.

- **SaveTransaction** – `.tmp` és `.bak` fájlokat használ az atomitás biztosításához
- **Javító** – automatikusan észleli a sérülést és helyreállítja biztonsági másolatokból
- **WAL (Előreíró Napló)** – rekordálja az inkrementális frissítéseket a teljes pillanatképek között

---

## 2.2.3 – pheap Párhuzamosság, GC és Biztonság

- **Párhuzamosság:** `RwLock` – több egyidejű olvasó, kizáró hozzáférés a tanítási lépésekhez
- **Szemétgyűjtés:** `CoreRegistry` – nyomon követi az aktív hivatkozásokat, megakadályozva a korai felszabadítást
- **Biztonság:** validálja az összes bemeneti dimenziót és a lebegőpontos értékek végességét

---

## 2.3 – OFTB: Ortogonális Fraktáltranszformációs Blokk

Az **OFTB** az RSF modell egyik legfontosabb komponense, amely biztosítja a globális kontextus-keverést a dimenziók között. Determinisztikus pillangó-keverési mechanizmust használ, amely megakadályozza a „halott csatorna" összeomlást azáltal, hogy a tenzor dimenzióit **1/√2 skálafaktorral** keveri össze.

Az OFTB blokk minden kapcsolási transzformációs réteg között alkalmazásra kerül, biztosítva, hogy az adatok mindkét fele végül kölcsönhatásba lépjen egymással. A pillangó-keverési minta felcseréli a tenzor elemeit egy specifikus séma szerint, majd rögzített skálázást alkalmaz – garantálva a matematikai invertálhatóság megmaradását.

---

## 3. fejezet – Hardvergyorsítás

A hardvergyorsítási réteg két fő komponensből áll:

1. Az **RSFAccelerator** felület – absztrahálja a hardveres műveleteket
2. A konkrét GPU implementációk – Futhark kernelek és CUDA kötések

### 3.1 – RSFAccelerator és Futhark Integráció

Az **RSFAccelerator** egy absztrakt interfész, amely definiálja az összes hardverspecifikus műveletet (inicializálás, előremeneti menet, inverz menet, tanítási lépések).

A **Futhark** kernelek a következő műveleteket valósítják meg:

- **Előremeneti menet** – az affin kapcsolási transzformáció kiszámítása
- **Inverz menet** – a bemenet pontos visszaállítása a kimenetből
- **Visszameneti menet** – a gradiensek számítása az összes súlyhoz és biashoz
- **OFTB műveletek** – a pillangó-keverési transzformáció végrehajtása

### 3.2 – CUDA Kötések és GPU Műveletek

A CUDA kötések (`cuda_bindings.zig`) a következő funkciókat biztosítják:

- GPU kontextus kezelés és inicializálás
- Memóriaallokáció és felszabadítás (`cudaMalloc`)
- Adatátvitel CPU és GPU között (`cudaMemcpy`)
- Kernel indítás és végrehajtási konfiguráció
- Szinkronizációs primitívek a párhuzamos végrehajtáshoz

---

## 4. fejezet – Elosztott Tanítás

### 4.1 – DistributedTrainerFuthark

A `DistributedTrainerFuthark` az elosztott tanítási rendszer központi koordinátora:

- **Adatkészlet felosztás** – az adatkészletet egyenletesen osztja el a GPU-k között
- **Modell inicializálás** – minden GPU-n azonos kezdeti súlyokkal inicializál
- **Szinkronizált tanítás** – koordinálja a tanítási lépéseket az összes GPU-n
- **Súly aggregálás** – a gradienseket összegyűjti és átlagolja a globális súlyfrissítéshez

### 4.2 – GPUCoordinator, NCCL és Modal Felhő

A `GPUCoordinator` az NCCL használatával kezeli az alacsony szintű GPU-kommunikációt.

**NCCL kollektív műveletek:**

| Művelet | Leírás |
|---|---|
| `allReduceFloat16` | Az összes GPU gradienseinek összegzése és elosztása 16 bites formátumban |
| `barrier` | Szinkronizációs pont az összes GPU között |
| `broadcast` | Adatszórás egyik GPU-ról az összes többire |

A **Modal** felhő integráció dinamikus GPU erőforrásokat biztosít, lehetővé téve a skálázást a keresletnek megfelelően.

### 4.3 – Elosztott Tartósság és WAL

**Biztonsági garanciák:**

- **Inkrementális biztonsági másolat** – minden tanítási lépés után rekord készül
- **Atomikus mentések** – a modellfájlok soha nem maradnak félig írt állapotban
- **Automatikus helyreállítás** – összeomlás után a rendszer visszaállítja a legutolsó konzisztens állapotot

---

## 5. fejezet – Formális Verifikáció

### 5.1 – Lean 4 Specifikációk

| Fájl | Tartalom |
|---|---|
| `rsf.lean` | A kapcsolási transzformáció bijectivitásának és az OFTB invertálhatóságának bizonyításai |
| `oftb_final.lean` | A pillangó-keverés matematikai helyességének bizonyításai |
| `rfs.lean` | Az Előremeneti/Inverz menetek pontosságának és a FixedQ (32.32 fixpontos) aritmetika helyességének bizonyításai |

**A Lean 4 bizonyítások garantálják:**
- Az RSF transzformációk szigorúan bijektívek
- Az előremeneti és inverz menetek pontosan inverzek egymásnak
- A fixpontos aritmetika nem vezet információvesztéshez

### 5.2 – Beluga, Mizar és Twelf Bizonyítások

| Eszköz | Fájl | Verifikációs Terület |
|---|---|---|
| **Beluga** | `rsf.bel` | „Regiszter Biztonság" – UAF hibák hiányának garantálása HOAS segítségével |
| **Mizar** | `rsf.miz` | Halmazelméleti specifikációk és bináris szerializációs logika |
| **Twelf** | – | Szerkezeti invertálhatóság és párhuzamos memóriamodell |

---

## 6. fejezet – Tesztelés és Összeomlás-helyreállítás

### 6.1 – Összeomlási Tesztsorozat

A tesztsorozat a következő forgatókönyveket fedi le:

- **Félbeszakított mentés** – a mentési folyamat megszakad a `.tmp` fájl írása közben
- **Sérült fejléc** – CRC32 ellenőrző összeg hibák észlelése
- **Hiányzó fájlok** – helyreállítás a `.bak` fájlból
- **WAL inkonzisztencia** – részleges rekordok kezelése
- **Memória szivárgás** – összeomlás utáni memóriaszivárgás ellenőrzése

### 6.2 – Javító és Helyreállító Alrendszer

**Komponensek:**
- **Repairer** – koordinálja a helyreállítási folyamatot CRC32 ellenőrzéssel
- **SnapshotRecovery** – megpróbálja betölteni a modellt az elsődleges elérési útról, sikertelenség esetén a biztonsági másolatból

**Helyreállítási folyamat:**

1. Az elsődleges fájl validálása (méret, fejléc CRC, hasznos adat CRC)
2. Ha érvénytelen → `.tmp` fájl ellenőrzése
3. Ha a `.tmp` érvényes → előléptetés elsődleges fájllá
4. Ha a `.tmp` is érvénytelen → visszaállítás a `.bak` fájlból
5. A biztonsági másolat validálása és az elsődleges fájl újraépítése

> Minden helyreállított paraméter átmegy a `ensureFiniteF32` biztonsági validáláson – NaN és Inf értékek nem kerülhetnek a modellbe.

---

## 7. fejezet – Szójegyzék

| Fogalom | Meghatározás |
|---|---|
| **RSF** (Reversible Scatter Flow) | Reverzibilis neurális hálózati architektúra bijektív transzformációkkal és O(1) memória-visszterjesztéssel |
| **OFTB** | Determinisztikus pillangó-keverési mechanizmus 1/√2 skálafaktorral a globális kontextus-keveréshez |
| **RSFLayer** | Az RSF modell egyedi rétege affin kapcsolási transzformációval (S és T paraméterek) |
| **RSFCore** | A pheap könyvtár központi struktúrája az RSF modell állapotának kezelésére |
| **LayerCore** | Egyedi réteg adatainak tárolása (súlyok, biasok, gradiensek, sebességek) |
| **pheap** | Gyártási minőségű futásidejű rendszer C-kompatibilis felülettel, tartóssággal és párhuzamossági kezeléssel |
| **RSFAccelerator** | Hardvergyorsítási absztrakciós felület a CPU és GPU közötti zökkenőmentes váltáshoz |
| **Futhark** | Funkcionális, adatpárhuzamos programozási nyelv GPU kernelek generálásához |
| **CUDA** | NVIDIA GPU programozási platform és API |
| **NCCL** | Optimalizált kollektív kommunikációs könyvtár több GPU-s rendszerekhez |
| **SaveTransaction** | Tranzakciós mentési mechanizmus `.tmp` és `.bak` fájlokkal az atomi mentések biztosításához |
| **WAL** (Write-Ahead Log) | Előreíró napló az állapotváltozások rögzítésére a pillanatképek között |
| **CRC32** | Ciklikus redundancia-ellenőrzés 32 bites adatintegritás-ellenőrzéshez |
| **Xavier Inicializálás** | Súlyinicializálási módszer a variancia fenntartásához a rétegek között |
| **Bijectív** | Pontosan invertálható transzformáció (injektív és szürjektív) |
| **Affin Kapcsolás** | Transzformáció ahol a bemenet két félre osztott, és az egyik fél a másik alapján transzformálódik |
| **Formális Verifikáció** | Matematikai bizonyítási módszerek a szoftver helyességének garantálására |
| **Lean 4** | Funkcionális programozási nyelv és formális verifikációs eszköz |
| **Beluga** | Formális verifikációs rendszer Magasabb Rendű Absztrakt Szintaxissal (HOAS) |
| **Mizar** | Matematikai formális nyelv és verifikációs rendszer |
| **Twelf** | Logikai keretrendszer formális bizonyításokhoz |
| **Tenzor** | Többdimenziós tömb – a neurális hálózatok alapvető adatszerkezete |
| **GPU** | Speciális hardver párhuzamos számításokhoz |
| **Modal** | Felhőalapú számítási platform dinamikus GPU erőforrásokkal |
| **DistributedTrainerFuthark** | Az elosztott tanítási rendszer központi koordinátora |
| **GPUCoordinator** | Alacsony szintű GPU kommunikációs koordinátor NCCL használatával |
| **Regiszter Biztonság** | Garancia arra, hogy a memóriaregiszterek nem kerülnek szabadításra használat közben |
| **UAF** (Use-After-Free) | Memóriabiztonsági hiba felszabadított memóriaterület elérésekor |
| **FixedQ** | 32.32 fixpontos aritmetikai formátum az RSF modellben |
