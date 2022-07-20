#include "curve448.h"
#include <stdint.h>
#include <stdio.h>


int main(int argc, char *argv[]) {
    uint32_t a[14];
    uint32_t b = 7;
    curve448SetInt(a, b);
    int loop;
    for(loop = 0; loop < 10; loop++)
      printf("%d ", a[loop]);
}