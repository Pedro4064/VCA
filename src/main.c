#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include "filter.h"
#include "pid.h"

#define WINDOW_SIZE 50

typedef struct STATES {
    float y;
    float dot_y;
    float ddot_y;
} states;

typedef struct MODEL {
    states current_state;
    states previous_states;
} model ;

typedef struct DATA_BUFFER {
    float data[WINDOW_SIZE];
    int index;
} data_buffer;

void data_buffer_reset(data_buffer* dbuff){
    memset(dbuff, 0, sizeof(data_buffer));
}

void data_buffer_insert(data_buffer* dbuff, float val){
    if(dbuff->index >= WINDOW_SIZE){
        memmove(&dbuff->data[0], &dbuff->data[1], sizeof(float)*(WINDOW_SIZE-1));
        dbuff->index--;
    }

    dbuff->data[dbuff->index++] = val;
}

float generate_white_noise(float amplitude) {
    // rand() returns 0..RAND_MAX, so convert to [-1, 1]
    float r = ((float)rand() / (float)RAND_MAX) * 2.0f - 1.0f;
    return r * amplitude;
}

int main(void){
    float Ts = 0.001;          /* Sampling/Update Period, in ms*/
    float num_steps = 1000000;    /* Total number of simulation steps, 1step=1ms*/
    float u = 1;              /* Current model input*/
    float u_previous = 0;     /* Previous model input*/
    float du = 0;             /* Derivative of model input*/

    data_buffer raw_data;
    float filtered_data[1];

    memset(&raw_data, 0, sizeof(raw_data));
    memset(&filtered_data, 0, sizeof(filtered_data));

    pid_controller pid;
    model example_model;

    for (int i = 0; i < num_steps; i++) {
        if (i == 0)
            u = 0;
        else 
            u = 1;

        du = (u - u_previous)/Ts;

        example_model.current_state.dot_y = example_model.previous_states.dot_y +
                                            example_model.previous_states.ddot_y * Ts;
        example_model.current_state.y = example_model.previous_states.y + 
                                        example_model.previous_states.dot_y * Ts +
                                        generate_white_noise(0.0002);

        example_model.current_state.ddot_y = du + 2*u - 
                                             example_model.current_state.dot_y - 
                                             example_model.current_state.y * 2;

        data_buffer_insert(&raw_data, example_model.current_state.y);
        if (i >= WINDOW_SIZE){
            f_moving_average_filter((float*)(&raw_data.data), WINDOW_SIZE, (float *)(&filtered_data), 1, WINDOW_SIZE);
        }
        printf("%f, %f, %f, %f, %f\n", example_model.current_state.y, example_model.current_state.dot_y, example_model.current_state.ddot_y, filtered_data[0], i*Ts);

        memcpy(&example_model.previous_states, &example_model.current_state, sizeof(states));
        u_previous = u;
    }


    return 0;
}