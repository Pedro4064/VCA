#include "pid.h"

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
}