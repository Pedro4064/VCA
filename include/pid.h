typedef struct PID_CONTROLLER {
  int ki;                    /* Integral Gain */
  int kp;                    /* Proportional Gain */
  int kd;                    /* Derivative Gain */
  int controller_saturation; /* The output variable saturation value */
  int target_value;          /* Target value of the controlled variable */
  int controlled_value;      /* Value of the controlled variable */
  int error_value;           /* Error between target and controlled value */
  int error_integral;        /* Integral of the error */
  int actuator_effort;       /* Value for the actuator effort */
  int Ts;                    /* Controller sampling/update period, in ms */
} pid_controller;

void pid_compute_actuator_command(pid_controller *pid_con);