#include <stdio.h>
#include "tommath.h"
int main(void){
  mp_int g,x,p,y; mp_init_multi(&g,&x,&p,&y,NULL);
  mp_set(&g,2); mp_set(&x,30);
  mp_set(&p,3); mp_mul_2d(&p,28,&p);
  int e = mp_exptmod(&g,&x,&p,&y);
  char buf[200]; mp_to_decimal(&y,buf,200);
  printf("err=%d y=%s used=%d is2k=%d is2kl=%d dr=%d\n",e,buf,p.used,mp_reduce_is_2k(&p),mp_reduce_is_2k_l(&p),mp_dr_is_modulus(&p));
  /* expected 2^30 mod 3*2^28 = 2^28 = 268435456 */
  return 0;
}
