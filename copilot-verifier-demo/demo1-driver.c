#include <stdint.h>
#include <stdio.h>
#include "demo1.h"

#define ITERATIONS 6

void even(uint32_t even_arg0) {
  printf("Even Fibonacci number: %d\n", even_arg0);
}

void odd(uint32_t odd_arg0) {
  printf("Odd  Fibonacci number: %d\n", odd_arg0);
}

int main(void) {
  for (int i = 0; i < ITERATIONS; i++) {
    step();
  }
  return 0;
}
