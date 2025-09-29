#include "filter.h"

#define WINDOW_SIZE 50


int main(void) {
  float raw_data[] = {10.4, 14.3, 15.3, 13.3, 45.32, 12, 15};
  float filtered_data[5];

  f_moving_average_filter(raw_data, 6, filtered_data, 5, 2);
}