#include "filter.h"
#include "pid.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WINDOW_SIZE 50

typedef struct STATES {
  float y;
  float dot_y;
  float ddot_y;
} states;

typedef struct MODEL {
  states current_state;
  states previous_states;
} model;

typedef struct DATA_BUFFER {
  float data[WINDOW_SIZE];
  int index;
} data_buffer;

void data_buffer_reset(data_buffer *dbuff) {
  memset(dbuff, 0, sizeof(data_buffer));
}

void data_buffer_insert(data_buffer *dbuff, float val) {
  if (dbuff->index >= WINDOW_SIZE) {
    memmove(&dbuff->data[0], &dbuff->data[1],
            sizeof(float) * (WINDOW_SIZE - 1));
    dbuff->index--;
  }

  dbuff->data[dbuff->index++] = val;
}

float generate_white_noise(float amplitude) {
  // rand() returns 0..RAND_MAX, so convert to [-1, 1]
  float r = ((float)rand() / (float)RAND_MAX) * 2.0f - 1.0f;
  return r * amplitude;
}

int main(void) {
  float Ts = 0.00001;        /* Sampling/Update Period, in ms*/
  float num_steps = 1000000; /* Total number of simulation steps, 1step=1ms*/
  float u = 1;               /* Current model input*/
  float u_previous = 0;      /* Previous model input*/
  float du = 0;              /* Derivative of model input*/

  model example_model;

  pid_controller pid;
  memset(&pid, 0, sizeof(pid_controller));
  pid.kp = 2.45;
  pid.ki = 2.1;
  pid.kd = 0.0631;
  pid.target_value = 1.0f;
  pid.Ts = Ts;

  for (int i = 0; i < num_steps; i++) {
    pid_compute_actuator_command(&pid);
    u = pid.actuator_effort;
    du = (u - u_previous) / Ts;

    example_model.current_state.dot_y =
        example_model.previous_states.dot_y +
        example_model.previous_states.ddot_y * Ts;

    example_model.current_state.y = example_model.previous_states.y +
                                    example_model.previous_states.dot_y * Ts;

    example_model.current_state.ddot_y = du + 2 * u -
                                         example_model.current_state.dot_y -
                                         example_model.current_state.y * 2;

    printf("%f, %f, %f, %f\n", example_model.current_state.y,
           example_model.current_state.dot_y,
           example_model.current_state.ddot_y, i * Ts);

    memcpy(&example_model.previous_states, &example_model.current_state,
           sizeof(states));
    u_previous = u;
    pid.controlled_value = example_model.current_state.y;
  }

  return 0;
}