#include <limits.h>
#include "main.h"


float f_sum(float* values, int length){
    float result = 0.0f;
    for(int i=0; i<length; i++)
        result+=values[i];
    return result;
}


void f_moving_average_filter(float* raw_data, unsigned int raw_data_length,
                          float* filtered_data, unsigned int filtered_data_length,
                          unsigned int window_size){
    
    for (unsigned int i = 0; i < filtered_data_length; i++) {
        filtered_data[i] = f_sum(raw_data+i, window_size)/window_size;
    }
}

