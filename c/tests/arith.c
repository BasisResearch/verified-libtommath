/* Differential driver: libtommath arithmetic on fixed operands, printed in
 * hex. Run on the Sail model and natively; the outputs
 * must be byte-identical. */
#include <stdio.h>
#include "tommath.h"

static const char *ops[] = {
    "0", "1", "-1", "FFFFFFF", "10000000", "-123456789ABCDEF0123456789",
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    "-DEADBEEFCAFEBABE0123456789ABCDEFFEDCBA9876543210",
    "1000000000000000000000000000000000000000000000000000000000001",
};
#define N (int)(sizeof ops / sizeof ops[0])

static void put(const char *tag, const mp_int *x) {
    char buf[1024];
    if (mp_to_radix(x, buf, sizeof buf, NULL, 16) != MP_OKAY) { printf("%s ERR\n", tag); return; }
    printf("%s %s\n", tag, buf);
}

int main(void) {
    mp_int a, b, c, d, m;
    if (mp_init_multi(&a, &b, &c, &d, &m, NULL) != MP_OKAY) return 1;
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            mp_read_radix(&a, ops[i], 16);
            mp_read_radix(&b, ops[j], 16);
            printf("# %d %d\n", i, j);
            mp_add(&a, &b, &c); put("add", &c);
            mp_sub(&a, &b, &c); put("sub", &c);
            mp_mul(&a, &b, &c); put("mul", &c);
            printf("cmp %d\n", mp_cmp(&a, &b));
            if (!mp_iszero(&b)) {
                mp_div(&a, &b, &c, &d); put("quo", &c); put("rem", &d);
                mp_mod(&a, &b, &c); put("mod", &c);
                mp_abs(&b, &m);
                if (mp_cmp_d(&m, 1) == MP_GT) {
                    mp_set(&d, 65537);
                    mp_exptmod(&a, &d, &m, &c); put("expmod", &c);
                }
            }
            mp_gcd(&a, &b, &c); put("gcd", &c);
        }
    }
    mp_clear_multi(&a, &b, &c, &d, &m, NULL);
    return 0;
}
