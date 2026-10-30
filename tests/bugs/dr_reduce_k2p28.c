/* mp_dr_reduce with n->dp[0] = 0: mp_dr_setup gives k = 2^28, not a digit, and
   mp_dr_reduce's fold stores the carry mu (up to 2^28) in x->dp[m] unmasked. The final s_mp_sub's borrow
   repairs it: on 600000 inputs x < radix^(2m) (m = 2, 3, 4; digits 0, MP_MASK, MP_MASK - 1 or random) the
   result equals x mod n and no non-digit stays behind. Expected output: "bad 0 / 600000, nondigit 0". */
#include <stdio.h>
#include <stdlib.h>
#include "tommath.h"
int main(void){
  mp_int n, x, y, r; mp_init_multi(&n, &x, &y, &r, NULL);
  int bad = 0, tot = 0, nondigit = 0;
  srand(1);
  for (int m = 2; m <= 4; m++) {
    mp_zero(&n); mp_grow(&n, m); for (int i = 1; i < m; i++) n.dp[i] = MP_MASK; n.dp[0] = 0; n.used = m; mp_clamp(&n);
    mp_digit k; mp_dr_setup(&n, &k);
    if (k != ((mp_digit)1 << MP_DIGIT_BIT)) printf("k = %lu\n", (unsigned long)k);
    for (int t = 0; t < 200000; t++) {
      mp_zero(&x); mp_grow(&x, 2 * m);
      for (int i = 0; i < 2 * m; i++) { int c = rand() % 4; x.dp[i] = c == 0 ? 0 : c == 1 ? MP_MASK : c == 2 ? (MP_MASK - 1) : (rand() & MP_MASK); }
      x.used = 2 * m; mp_clamp(&x);
      mp_copy(&x, &y);
      mp_dr_reduce(&x, &n, k);
      mp_mod(&y, &n, &r);
      tot++;
      for (int i = 0; i < x.alloc; i++) if (x.dp[i] > MP_MASK) { nondigit++; break; }
      if (mp_cmp(&x, &r) != MP_EQ) bad++;
    }
  }
  printf("bad %d / %d, nondigit %d\n", bad, tot, nondigit);
  return 0;
}
