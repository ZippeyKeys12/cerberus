#include "cerberus.h"
/* Generated by CIL v. 1.7.3 */
/* print_CIL_Input is false */

extern void abort(void) ;
__inline static unsigned short foo(unsigned int *p ) 
{ 


  {
  return (*p);
}
}
unsigned int u  ;
int main(void) 
{ 
  unsigned short tmp ;

  {
  tmp = foo(& u);
  if (((int )tmp & 32768) != 0) {
    abort();
  }
  return (0);
}
}
