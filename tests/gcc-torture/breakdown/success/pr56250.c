#include "cerberus.h"
/* PR tree-optimization/56250 */


int 
main (void)
{
  unsigned int x = 2;
  unsigned int y = (0U - x / 2) / 2;
  if (-1U / x != y)
    abort ();
  return 0;
}
