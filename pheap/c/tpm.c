#include "cache_flush.h"

#include <math.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <time.h>

#if defined(RSF_ARCH_X86_64)
#include <emmintrin.h>
#include <immintrin.h>
#include <x86intrin.h>
#endif

static uint32_t rsf_crc32_table[256];
static int rsf_crc32_table_ready = 0;

static void rsf_crc32_table_init(void) {
    if (rsf_crc32_table_ready) return;
    for (uint32_t i = 0; i < 256; ++i) {
        uint32_t c = i;
        for (int k = 0; k < 8; ++k) {
            c = (c & 1) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
        }
        rsf_crc32_table[i] = c;
    }
    rsf_crc32_table_ready = 1;
}

uint32_t rsf_crc32_init(void) {
    rsf_crc32_table_init();
    return 0xFFFFFFFFu;
}

uint32_t rsf_crc32_update(uint32_t crc, const void *data, size_t length) {
    rsf_crc32_table_init();
    const uint8_t *p = (const uint8_t *)data;
    for (size_t i = 0; i < length; ++i) {
        crc = rsf_crc32_table[(crc ^ p[i]) & 0xFFu] ^ (crc >> 8);
    }
    return crc;
}

uint32_t rsf_crc32_finish(uint32_t crc) {
    return crc ^ 0xFFFFFFFFu;
}

uint32_t rsf_crc32_compute(const void *data, size_t length) {
    uint32_t crc = rsf_crc32_init();
    crc = rsf_crc32_update(crc, data, length);
    return rsf_crc32_finish(crc);
}

void rsf_cache_clwb(const void *addr) {
#if defined(RSF_ARCH_X86_64)
    _mm_clflushopt((void *)addr);
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dc cvac, %0" :: "r"(addr) : "memory");
#else
    (void)addr;
#endif
}

void rsf_cache_clflushopt(const void *addr) {
#if defined(RSF_ARCH_X86_64)
    _mm_clflushopt((void *)addr);
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dc civac, %0" :: "r"(addr) : "memory");
#else
    (void)addr;
#endif
}

void rsf_cache_clflush(const void *addr) {
#if defined(RSF_ARCH_X86_64)
    _mm_clflush((void *)addr);
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dc civac, %0" :: "r"(addr) : "memory");
#else
    (void)addr;
#endif
}

void rsf_cache_sfence(void) {
#if defined(RSF_ARCH_X86_64)
    _mm_sfence();
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dmb ishst" ::: "memory");
#else
    __atomic_thread_fence(__ATOMIC_RELEASE);
#endif
}

void rsf_cache_lfence(void) {
#if defined(RSF_ARCH_X86_64)
    _mm_lfence();
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dmb ishld" ::: "memory");
#else
    __atomic_thread_fence(__ATOMIC_ACQUIRE);
#endif
}

void rsf_cache_mfence(void) {
#if defined(RSF_ARCH_X86_64)
    _mm_mfence();
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("dmb ish" ::: "memory");
#else
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
#endif
}

size_t rsf_cacheline_size(void) {
    return 64;
}

void rsf_persist_range(const void *addr, size_t length) {
    if (length == 0) return;
    const size_t cl = rsf_cacheline_size();
    const uintptr_t start = (uintptr_t)addr & ~(uintptr_t)(cl - 1);
    const uintptr_t end = (uintptr_t)addr + length;
    for (uintptr_t p = start; p < end; p += cl) {
        rsf_cache_clwb((const void *)p);
    }
    rsf_cache_sfence();
}

void rsf_drain(void) {
    rsf_cache_sfence();
}

int rsf_finite_f32_slice(const float *data, size_t length) {
    for (size_t i = 0; i < length; ++i) {
        const float v = data[i];
        if (!isfinite(v)) return 0;
    }
    return 1;
}

int rsf_finite_f64_slice(const double *data, size_t length) {
    for (size_t i = 0; i < length; ++i) {
        const double v = data[i];
        if (!isfinite(v)) return 0;
    }
    return 1;
}

void rsf_prefetch_read(const void *addr) {
    __builtin_prefetch(addr, 0, 3);
}

void rsf_prefetch_write(const void *addr) {
    __builtin_prefetch(addr, 1, 3);
}

void rsf_memzero_persistent(void *addr, size_t length) {
    memset(addr, 0, length);
    rsf_persist_range(addr, length);
}

void rsf_memcopy_persistent(void *dst, const void *src, size_t length) {
    memcpy(dst, src, length);
    rsf_persist_range(dst, length);
}

void rsf_memset_aligned(void *addr, int value, size_t length) {
    memset(addr, value, length);
}

uint64_t rsf_rdtsc(void) {
#if defined(RSF_ARCH_X86_64)
    return (uint64_t)__rdtsc();
#elif defined(RSF_ARCH_AARCH64)
    uint64_t v;
    asm volatile("mrs %0, cntvct_el0" : "=r"(v));
    return v;
#else
    return rsf_monotonic_ns();
#endif
}

uint64_t rsf_monotonic_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

void rsf_pause(void) {
#if defined(RSF_ARCH_X86_64)
    _mm_pause();
#elif defined(RSF_ARCH_AARCH64)
    asm volatile("yield" ::: "memory");
#else
    __asm__ __volatile__("" ::: "memory");
#endif
}

void rsf_compiler_barrier(void) {
    __asm__ __volatile__("" ::: "memory");
}

float rsf_clip_f32(float x, float lo, float hi) {
    if (x < lo) return lo;
    if (x > hi) return hi;
    return x;
}

double rsf_clip_f64(double x, double lo, double hi) {
    if (x < lo) return lo;
    if (x > hi) return hi;
    return x;
}

void rsf_axpy_f32(float *dst, const float *src, float alpha, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        dst[i] = dst[i] + alpha * src[i];
    }
}

void rsf_scal_f32(float *dst, float alpha, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        dst[i] = dst[i] * alpha;
    }
}

float rsf_dot_f32(const float *a, const float *b, size_t n) {
    float acc = 0.0f;
    for (size_t i = 0; i < n; ++i) {
        const float p = a[i] * b[i];
        if (!isnan(p)) acc += p;
    }
    return acc;
}

float rsf_sum_sq_f32(const float *a, size_t n) {
    float acc = 0.0f;
    for (size_t i = 0; i < n; ++i) {
        acc += a[i] * a[i];
    }
    return acc;
}
