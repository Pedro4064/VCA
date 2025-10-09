typedef struct PID_CONTROLLER {
  float ki;                    /* Integral Gain */
  float kp;                    /* Proportional Gain */
  float kd;                    /* Derivative Gain */
  float controller_saturation; /* The output variable saturation value */
  float target_value;          /* Target value of the controlled variable */
  float controlled_value;      /* Value of the controlled variable */
  float error_value;           /* Error between target and controlled value */
  float error_integral;        /* Integral of the error */
  float error_integral_ub;     /* Upper bound of error integral */
  float error_integral_lb;     /* Lower bound of error integral */
  float actuator_effort;       /* Value for the actuator effort */
  float Ts;                    /* Controller sampling/update period, in ms */
} pid_controller;

void pid_compute_actuator_command(pid_controller *pid_con);