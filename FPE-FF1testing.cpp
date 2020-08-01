#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <openssl/aes.h>
#include <openssl/crypto.h>
#include <openssl/bn.h>
#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "crypt32.lib")

#define FPE_ENCRYPT 1
#define FPE_DECRYPT 0

#define FF1_ROUNDS 10

struct fpe_key_st
{
  unsigned int radix;
  unsigned int tweaklen;
  unsigned char *tweak;
  AES_KEY aes_enc_ctx;
};

typedef struct fpe_key_st FPE_KEY;

// ceil and floor for x / (2 ^ bit)
#define ceil2(x, bit) (((x) >> (bit)) + (((x) & ((1 << (bit)) - 1)) > 0))
#define floor2(x, bit) ((x) >> (bit))

void pow_uv(BIGNUM *pow_u, BIGNUM *pow_v, unsigned int x, int u, int v, BN_CTX *ctx)
{
  BN_CTX_start(ctx);
  BIGNUM *base = BN_CTX_get(ctx),
         *e = BN_CTX_get(ctx);

  BN_set_word(base, x);
  if (u > v)
  {
    BN_set_word(e, v);
    BN_exp(pow_v, base, e, ctx);
    BN_mul(pow_u, pow_v, base, ctx);
  }
  else
  {
    BN_set_word(e, u);
    BN_exp(pow_u, base, e, ctx);
    if (u == v)
      BN_copy(pow_v, pow_u);
    else
      BN_mul(pow_v, pow_u, base, ctx);
  }

  BN_CTX_end(ctx);
  return;
}

// convert numeral string to number
void str2num(BIGNUM *Y, const unsigned int *X, unsigned long long radix, unsigned int len, BN_CTX *ctx)
{
  BN_CTX_start(ctx);
  BIGNUM *r = BN_CTX_get(ctx),
         *x = BN_CTX_get(ctx);

  BN_set_word(Y, 0);
  BN_set_word(r, radix);
  for (int i = 0; i < len; ++i)
  {
    // Y = Y * radix + X[i]
    BN_set_word(x, X[i]);
    BN_mul(Y, Y, r, ctx);
    BN_add(Y, Y, x);
  }

  BN_CTX_end(ctx);
  return;
}

// convert number to numeral string
void num2str(const BIGNUM *X, unsigned int *Y, unsigned int radix, int len, BN_CTX *ctx)
{
  BN_CTX_start(ctx);
  BIGNUM *dv = BN_CTX_get(ctx),
         *rem = BN_CTX_get(ctx),
         *r = BN_CTX_get(ctx),
         *XX = BN_CTX_get(ctx);

  BN_copy(XX, X);
  BN_set_word(r, radix);
  memset(Y, 0, len << 2);

  for (int i = len - 1; i >= 0; --i)
  {
    // XX / r = dv ... rem
    BN_div(dv, rem, XX, r, ctx);
    // Y[i] = XX % r
    Y[i] = BN_get_word(rem);
    // XX = XX / r
    BN_copy(XX, dv);
  }

  BN_CTX_end(ctx);
  return;
}

void FF1_encrypt(const unsigned int *in, unsigned int *out, AES_KEY *aes_enc_ctx, const unsigned char *tweak, const unsigned int radix, size_t inlen, size_t tweaklen)
{
  BIGNUM *bnum = BN_new(),
         *y = BN_new(),
         *c = BN_new(),
         *anum = BN_new(),
         *qpow_u = BN_new(),
         *qpow_v = BN_new();
  BN_CTX *ctx = BN_CTX_new();
  printf("========== FF1  1 ==========\n");
  union {
    long one;
    char little;
  } is_endian = {1};

  memcpy(out, in, inlen << 2);
  int u = floor2(inlen, 1);
  int v = inlen - u;
  unsigned int *A = out, *B = out + u;
  pow_uv(qpow_u, qpow_v, radix, u, v, ctx);
  printf("========== FF1  2 ==========\n");
  unsigned int temp = (unsigned int)ceil(v * log2(radix));
  const int b = ceil2(temp, 3);
  const int d = 4 * ceil2(b, 2) + 4;

  int pad = ((-tweaklen - b - 1) % 16 + 16) % 16;
  int Qlen = tweaklen + pad + 1 + b;
  unsigned char P[16];
  unsigned char *Q = (unsigned char *)OPENSSL_malloc(Qlen), *Bytes = (unsigned char *)OPENSSL_malloc(b);

  // initialize P
  P[0] = 0x1;
  P[1] = 0x2;
  P[2] = 0x1;
  P[7] = u % 256;
  if (is_endian.little)
  {
    temp = (radix << 8) | 10;
    P[3] = (temp >> 24) & 0xff;
    P[4] = (temp >> 16) & 0xff;
    P[5] = (temp >> 8) & 0xff;
    P[6] = temp & 0xff;
    P[8] = (inlen >> 24) & 0xff;
    P[9] = (inlen >> 16) & 0xff;
    P[10] = (inlen >> 8) & 0xff;
    P[11] = inlen & 0xff;
    P[12] = (tweaklen >> 24) & 0xff;
    P[13] = (tweaklen >> 16) & 0xff;
    P[14] = (tweaklen >> 8) & 0xff;
    P[15] = tweaklen & 0xff;
  }
  else
  {
    *((unsigned int *)(P + 3)) = (radix << 8) | 10;
    *((unsigned int *)(P + 8)) = inlen;
    *((unsigned int *)(P + 12)) = tweaklen;
  }

  // initialize Q
  memcpy(Q, tweak, tweaklen);
  memset(Q + tweaklen, 0x00, pad);
  assert(tweaklen + pad - 1 <= Qlen);
  printf("========== FF1  3 ==========\n");
  unsigned char R[16];
  int cnt = ceil2(d, 4) - 1;
  int Slen = 16 + cnt * 16;
  unsigned char *S = (unsigned char *)OPENSSL_malloc(Slen);
  for (int i = 0; i < FF1_ROUNDS; ++i)
  {
    // v
    int m = (i & 1) ? v : u;
    printf("========== FF1  4 ==========\n");
    // i
    Q[tweaklen + pad] = i & 0xff;
    str2num(bnum, B, radix, inlen - m, ctx);
    int BytesLen = BN_bn2bin(bnum, Bytes);
    memset(Q + Qlen - b, 0x00, b);

    int qtmp = Qlen - BytesLen;
    memcpy(Q + qtmp, Bytes, BytesLen);

    // ii PRF(P || Q), P is always 16 bytes long
    AES_encrypt(P, R, aes_enc_ctx);
    printf("========== FF1  5 ==========\n");
    int count = Qlen / 16;
    unsigned char Ri[16];
    unsigned char *Qi = Q;
    for (int cc = 0; cc < count; ++cc)
    {
      for (int j = 0; j < 16; ++j)
        Ri[j] = Qi[j] ^ R[j];
      AES_encrypt(Ri, R, aes_enc_ctx);
      Qi += 16;
    }

    // iii
    unsigned char tmp[16], SS[16];
    memset(S, 0x00, Slen);
    assert(Slen >= 16);
    memcpy(S, R, 16);
    for (int j = 1; j <= cnt; ++j)
    {
      memset(tmp, 0x00, 16);

      if (is_endian.little)
      {
        // convert to big endian
        // full unroll
        tmp[15] = j & 0xff;
        tmp[14] = (j >> 8) & 0xff;
        tmp[13] = (j >> 16) & 0xff;
        tmp[12] = (j >> 24) & 0xff;
      }
      else
        *((unsigned int *)tmp + 3) = j;

      for (int k = 0; k < 16; ++k)
        tmp[k] ^= R[k];
      AES_encrypt(tmp, SS, aes_enc_ctx);
      assert((S + 16 * j)[0] == 0x00);
      assert(16 + 16 * j <= Slen);
      memcpy(S + 16 * j, SS, 16);
    }

    // iv
    BN_bin2bn(S, d, y);
    // vi
    // (num(A, radix, m) + y) % qpow(radix, m);
    str2num(anum, A, radix, m, ctx);
    // anum = (anum + y) mod qpow_uv
    if (m == u)
      BN_mod_add(c, anum, y, qpow_u, ctx);
    else
      BN_mod_add(c, anum, y, qpow_v, ctx);

    // swap A and B
    assert(A != B);
    A = (unsigned int *)((uintptr_t)A ^ (uintptr_t)B);
    B = (unsigned int *)((uintptr_t)B ^ (uintptr_t)A);
    A = (unsigned int *)((uintptr_t)A ^ (uintptr_t)B);
    num2str(c, B, radix, m, ctx);
  }
  printf("========== FF1 encrypt==========\n");

  // free the space
  BN_clear_free(anum);
  BN_clear_free(bnum);
  BN_clear_free(c);
  BN_clear_free(y);
  BN_clear_free(qpow_u);
  BN_clear_free(qpow_v);
  BN_CTX_free(ctx);
  OPENSSL_free(Bytes);
  OPENSSL_free(Q);
  OPENSSL_free(S);
  return;
}

void FF1_decrypt(const unsigned int *in, unsigned int *out, AES_KEY *aes_enc_ctx, const unsigned char *tweak, const unsigned int radix, size_t inlen, size_t tweaklen)
{
  printf("========== FF1 decrypt ==========\n");
  BIGNUM *bnum = BN_new(),
         *y = BN_new(),
         *c = BN_new(),
         *anum = BN_new(),
         *qpow_u = BN_new(),
         *qpow_v = BN_new();
  BN_CTX *ctx = BN_CTX_new();

  union {
    long one;
    char little;
  } is_endian = {1};

  memcpy(out, in, inlen << 2);
  int u = floor2(inlen, 1);
  int v = inlen - u;
  unsigned int *A = out, *B = out + u;
  pow_uv(qpow_u, qpow_v, radix, u, v, ctx);

  unsigned int temp = (unsigned int)ceil(v * log2(radix));
  const int b = ceil2(temp, 3);
  const int d = 4 * ceil2(b, 2) + 4;

  int pad = ((-tweaklen - b - 1) % 16 + 16) % 16;
  int Qlen = tweaklen + pad + 1 + b;
  unsigned char P[16];
  unsigned char *Q = (unsigned char *)OPENSSL_malloc(Qlen), *Bytes = (unsigned char *)OPENSSL_malloc(b);
  // initialize P
  P[0] = 0x1;
  P[1] = 0x2;
  P[2] = 0x1;
  P[7] = u % 256;
  if (is_endian.little)
  {
    temp = (radix << 8) | 10;
    P[3] = (temp >> 24) & 0xff;
    P[4] = (temp >> 16) & 0xff;
    P[5] = (temp >> 8) & 0xff;
    P[6] = temp & 0xff;
    P[8] = (inlen >> 24) & 0xff;
    P[9] = (inlen >> 16) & 0xff;
    P[10] = (inlen >> 8) & 0xff;
    P[11] = inlen & 0xff;
    P[12] = (tweaklen >> 24) & 0xff;
    P[13] = (tweaklen >> 16) & 0xff;
    P[14] = (tweaklen >> 8) & 0xff;
    P[15] = tweaklen & 0xff;
  }
  else
  {
    *((unsigned int *)(P + 3)) = (radix << 8) | 10;
    *((unsigned int *)(P + 8)) = inlen;
    *((unsigned int *)(P + 12)) = tweaklen;
  }

  // initialize Q
  memcpy(Q, tweak, tweaklen);
  memset(Q + tweaklen, 0x00, pad);
  assert(tweaklen + pad - 1 <= Qlen);

  unsigned char R[16];
  int cnt = ceil2(d, 4) - 1;
  int Slen = 16 + cnt * 16;
  unsigned char *S = (unsigned char *)OPENSSL_malloc(Slen);
  for (int i = FF1_ROUNDS - 1; i >= 0; --i)
  {
    // v
    int m = (i & 1) ? v : u;

    // i
    Q[tweaklen + pad] = i & 0xff;
    str2num(anum, A, radix, inlen - m, ctx);
    memset(Q + Qlen - b, 0x00, b);
    int BytesLen = BN_bn2bin(anum, Bytes);
    int qtmp = Qlen - BytesLen;
    memcpy(Q + qtmp, Bytes, BytesLen);

    // ii PRF(P || Q)
    memset(R, 0x00, sizeof(R));
    AES_encrypt(P, R, aes_enc_ctx);
    int count = Qlen / 16;
    unsigned char Ri[16];
    unsigned char *Qi = Q;
    for (int cc = 0; cc < count; ++cc)
    {
      for (int j = 0; j < 16; ++j)
        Ri[j] = Qi[j] ^ R[j];
      AES_encrypt(Ri, R, aes_enc_ctx);
      Qi += 16;
    }

    // iii
    unsigned char tmp[16], SS[16];
    memset(S, 0x00, Slen);
    memcpy(S, R, 16);
    for (int j = 1; j <= cnt; ++j)
    {
      memset(tmp, 0x00, 16);

      if (is_endian.little)
      {
        // convert to big endian
        // full unroll
        tmp[15] = j & 0xff;
        tmp[14] = (j >> 8) & 0xff;
        tmp[13] = (j >> 16) & 0xff;
        tmp[12] = (j >> 24) & 0xff;
      }
      else
        *((unsigned int *)tmp + 3) = j;

      for (int k = 0; k < 16; ++k)
        tmp[k] ^= R[k];
      AES_encrypt(tmp, SS, aes_enc_ctx);
      assert((S + 16 * j)[0] == 0x00);
      memcpy(S + 16 * j, SS, 16);
    }

    // iv
    BN_bin2bn(S, d, y);
    // vi
    // (num(B, radix, m) - y) % qpow(radix, m);
    str2num(bnum, B, radix, m, ctx);
    if (m == u)
      BN_mod_sub(c, bnum, y, qpow_u, ctx);
    else
      BN_mod_sub(c, bnum, y, qpow_v, ctx);

    // swap A and B
    assert(A != B);
    A = (unsigned int *)((uintptr_t)A ^ (uintptr_t)B);
    B = (unsigned int *)((uintptr_t)B ^ (uintptr_t)A);
    A = (unsigned int *)((uintptr_t)A ^ (uintptr_t)B);
    num2str(c, A, radix, m, ctx);
  }

  // free the space
  BN_clear_free(anum);
  BN_clear_free(bnum);
  BN_clear_free(y);
  BN_clear_free(c);
  BN_clear_free(qpow_u);
  BN_clear_free(qpow_v);
  BN_CTX_free(ctx);
  OPENSSL_free(Bytes);
  OPENSSL_free(Q);
  OPENSSL_free(S);
  return;
}

int FPE_set_ff1_key(const unsigned char *userKey, const int bits, const unsigned char *tweak, const unsigned int tweaklen, const int radix, FPE_KEY *key)
{
  int ret;
  if (bits != 128 && bits != 192 && bits != 256)
  {
    ret = -1;
    return ret;
  }
  key->radix = radix;
  key->tweaklen = tweaklen;
  key->tweak = (unsigned char *)OPENSSL_malloc(tweaklen);
  memcpy(key->tweak, tweak, tweaklen);
  ret = AES_set_encrypt_key(userKey, bits, &key->aes_enc_ctx);
  return ret;
}

void FPE_unset_ff1_key(FPE_KEY *key)
{
  OPENSSL_free(key->tweak);
}

void FPE_ff1_encrypt(unsigned int *in, unsigned int *out, unsigned int inlen, FPE_KEY *key, const int enc)
{
  if (enc)
    FF1_encrypt(in, out, &key->aes_enc_ctx, key->tweak,
                key->radix, inlen, key->tweaklen);

  else
    FF1_decrypt(in, out, &key->aes_enc_ctx, key->tweak,
                key->radix, inlen, key->tweaklen);
}

void hex2chars(unsigned char hex[], unsigned char result[])
{
  int len = strlen(reinterpret_cast<const char *>(hex));
  unsigned char temp[3];
  temp[2] = 0x00;

  int j = 0;
  for (int i = 0; i < len; i += 2)
  {
    temp[0] = hex[i];
    temp[1] = hex[i + 1];
    result[j] = (char)strtol(reinterpret_cast<const char *>(temp), NULL, 16);
    ++j;
  }
}

void map_chars(unsigned char str[], unsigned int result[])
{
  int len = strlen(reinterpret_cast<const char *>(str));

  for (int i = 0; i < len; ++i)
    if (str[i] >= 'a')
      result[i] = str[i] - 'a' + 10;
    else
      result[i] = str[i] - '0';
}

void inverse_map_chars(unsigned result[], unsigned char str[], int len)
{
  for (int i = 0; i < len; ++i)
    if (result[i] < 10)
      str[i] = result[i] + '0';
    else
      str[i] = result[i] - 10 + 'a';

  str[len] = 0x00;
}

int main(int argc, char *argv[])
{
  if (argc != 5)
  {
    printf("Usage: %s <key> <tweak> <radix> <plaintext>\n", argv[0]);
    return 0;
  }

  unsigned char k[100],
      t[100],
      result[100];
  int xlen = strlen(argv[4]),
      klen = strlen(argv[1]) / 2,
      tlen = strlen(argv[2]) / 2,
      radix = atoi(argv[3]);
  unsigned int x[100],
      y[100];

  hex2chars(reinterpret_cast<unsigned char *>(argv[1]), k);
  hex2chars(reinterpret_cast<unsigned char *>(argv[2]), t);
  map_chars(reinterpret_cast<unsigned char *>(argv[4]), x);

  for (int i = 0; i < xlen; ++i)
    assert(x[i] < radix);

  FPE_KEY ff1;

  printf("key:");
  for (int i = 0; i < klen; ++i)
    printf(" %02x", k[i]);
  puts("");
  if (tlen)
    printf("tweak:");
  for (int i = 0; i < tlen; ++i)
    printf(" %02x", t[i]);
  if (tlen)
    puts("");

  FPE_set_ff1_key(k, klen * 8, t, tlen, radix, &ff1);

  printf("after map: ");
  for (int i = 0; i < xlen; ++i)
    printf(" %d", x[i]);
  printf("\n\n");

  printf("========== FF1 ==========\n");
  FPE_ff1_encrypt(x, y, xlen, &ff1, FPE_ENCRYPT);

  printf("ciphertext(numeral string):");
  for (int i = 0; i < xlen; ++i)
    printf(" %d", y[i]);
  printf("\n");

  inverse_map_chars(y, result, xlen);
  printf("ciphertext: %s\n\n", result);

  memset(x, 0, sizeof(x));
  FPE_ff1_encrypt(y, x, xlen, &ff1, FPE_DECRYPT);

  printf("plaintext:");
  for (int i = 0; i < xlen; ++i)
    printf(" %d", x[i]);
  printf("\n\n");

  FPE_unset_ff1_key(&ff1);

  return 0;
}
