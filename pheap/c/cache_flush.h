#ifndef RSF_CACHE_FLUSH_H
#define RSF_CACHE_FLUSH_H

#include <stddef.h>
#include <stdint.h>

#if defined(__x86_64__) || defined(_M_X64)
#define RSF_ARCH_X86_64 1
#elif defined(__aarch64__) || defined(_M_ARM64)
#define RSF_ARCH_AARCH64 1
#else
#define RSF_ARCH_GENERIC 1
#endif

#ifdef __cplusplus
extern "C" {
#endif

void rsf_cache_clwb(const void *addr);
void rsf_cache_clflushopt(const void *addr);
void rsf_cache_clflush(const void *addr);
void rsf_cache_sfence(void);
void rsf_cache_lfence(void);
void rsf_cache_mfence(void);
void rsf_persist_range(const void *addr, size_t length);
void rsf_drain(void);
size_t rsf_cacheline_size(void);

uint32_t rsf_crc32_init(void);
uint32_t rsf_crc32_update(uint32_t crc, const void *data, size_t length);
uint32_t rsf_crc32_finish(uint32_t crc);
uint32_t rsf_crc32_compute(const void *data, size_t length);

int rsf_finite_f32_slice(const float *data, size_t length);
int rsf_finite_f64_slice(const double *data, size_t length);

void rsf_prefetch_read(const void *addr);
void rsf_prefetch_write(const void *addr);

void rsf_memzero_persistent(void *addr, size_t length);
void rsf_memcopy_persistent(void *dst, const void *src, size_t length);
void rsf_memset_aligned(void *addr, int value, size_t length);

uint64_t rsf_rdtsc(void);
uint64_t rsf_monotonic_ns(void);

void rsf_pause(void);
void rsf_compiler_barrier(void);

float rsf_clip_f32(float x, float lo, float hi);
double rsf_clip_f64(double x, double lo, double hi);

void rsf_axpy_f32(float *dst, const float *src, float alpha, size_t n);
void rsf_scal_f32(float *dst, float alpha, size_t n);
float rsf_dot_f32(const float *a, const float *b, size_t n);
float rsf_sum_sq_f32(const float *a, size_t n);

#ifdef __cplusplus
}
#endif

#endif
