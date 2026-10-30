#include <stdio.h>
#include "tommath.h"
static void pr(const char*s, mp_int*a){char b[300]; mp_to_decimal(a,b,300); printf("%s=%s ",s,b);}
int main(void){
  mp_int a,b,c,x,y; mp_init_multi(&a,&b,&c,&x,&y,NULL);
  mp_set(&a,3); mp_neg(&a,&a); mp_set(&b,7);
  int e=mp_invmod(&a,&b,&c); printf("err=%d ",e); pr("invmod(-3,7)",&c); printf("\n");
  mp_set(&b,8); e=mp_invmod(&a,&b,&c); printf("err=%d ",e); pr("invmod(-3,8)",&c); printf("\n");
  /* exptmod with negative exponent */
  mp_set(&a,3); mp_neg(&a,&a); mp_set(&x,1); mp_neg(&x,&x); mp_set(&b,7);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("(-3)^-1 mod 7",&y); printf("\n");
  mp_set(&x,2); mp_neg(&x,&x);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("(-3)^-2 mod 7",&y); printf("\n");
  mp_set(&x,1); mp_neg(&x,&x); mp_set(&b,8);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("(-3)^-1 mod 8",&y); printf("\n");
  /* exptmod negative base positive exp */
  mp_set(&x,3);  mp_set(&b,7);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("(-3)^3 mod 7",&y); printf("\n");
  mp_set(&a,5); mp_set(&x,0); mp_set(&b,1);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("5^0 mod 1",&y); printf("\n");
  mp_set(&b,6);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("5^0 mod 6",&y); printf("\n");
  mp_set(&b,7);
  e=mp_exptmod(&a,&x,&b,&y); printf("err=%d ",e); pr("5^0 mod 7",&y); printf("\n");
  mp_set(&a,3); mp_set(&b,9); e=mp_invmod(&a,&b,&c); printf("err=%d (3,9)\n",e);
  mp_set(&a,0); mp_set(&b,9); e=mp_invmod(&a,&b,&c); printf("err=%d (0,9)\n",e);
  mp_set(&a,1); mp_set(&b,2); e=mp_invmod(&a,&b,&c); printf("err=%d ",e); pr("inv(1,2)",&c); printf("\n");
  mp_set(&a,3); mp_set(&b,2); e=mp_invmod(&a,&b,&c); printf("err=%d ",e); pr("inv(3,2)",&c); printf("\n");
  mp_set(&a,4); mp_set(&b,2); e=mp_invmod(&a,&b,&c); printf("err=%d (4,2)\n",e);
  mp_set(&a,4); mp_set(&b,6); e=mp_invmod(&a,&b,&c); printf("err=%d (4,6)\n",e);
  mp_set(&a,3); mp_set(&b,6); e=mp_invmod(&a,&b,&c); printf("err=%d (3,6) ",e);pr("c",&c);printf("\n");
  mp_set(&a,6); mp_set(&b,6); e=mp_invmod(&a,&b,&c); printf("err=%d (6,6) ",e);pr("c",&c);printf("\n");
  return 0;
}
