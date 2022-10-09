#include <stdint.h>
#include <stdio.h>
#include "demo2.h"

uint8_t temperature;

#define ITERATIONS 4
uint8_t temperature_vals[ITERATIONS] = { 100, 120, 120, 120 };

void heaton(float heaton_arg0) {
  printf("Temperature below 18.0: %f\n", heaton_arg0);
}

void heatoff(float heatoff_arg0) {
  printf("Temperature above 21.0: %f\n", heatoff_arg0);
}

int main(void) {
  for (int i = 0; i < ITERATIONS; i++) {
    temperature = temperature_vals[i];
    step();
  }
  return 0;
}
