#include "pid.h"
#include <string.h>
#include <stdio.h>

typedef struct STATES {
    int y;
    int dot_y;
    int ddot_y;
} states;

typedef struct MODEL {
    states current_state;
    states previous_states;
} model ;

int main(void){
    int Ts = 1;             /* Sampling/Update Period, in ms*/
    int num_steps = 100000; /* Total number of simulation steps, 1step=1ms*/
    int u = 1;              /* Current model input*/
    int u_previous = 0;     /* Previous model input*/
    int du = 0;             /* Derivative of model input*/

    pid_controller pid;
    memset(&pid, 0, sizeof(pid_controller));
    model example_model;
    memset(&example_model, 0, sizeof(model));

    for (int i = 0; i < num_steps; i++) {
        if (i == 0)
            u = 0;
        else 
            u = 1;

        du = (u - u_previous)/Ts;
        example_model.current_state.dot_y = example_model.previous_states.dot_y +
                                            example_model.previous_states.ddot_y * Ts;
        example_model.current_state.y = example_model.previous_states.y + 
                                        example_model.previous_states.dot_y * Ts;
        example_model.current_state.ddot_y = du + 2*u - 
                                             example_model.current_state.dot_y - 
                                             example_model.current_state.y * 2;

        printf("%d, %d, %d\n", example_model.current_state.y, example_model.current_state.dot_y, example_model.current_state.ddot_y);

        memcpy(&example_model.previous_states, &example_model.current_state, sizeof(states));
        u_previous = u;
    }


    return 0;
}