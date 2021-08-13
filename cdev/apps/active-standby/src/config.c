#include "app.h"
#include <stdint.h>

const uint64_t PALS_PERIOD = 100000000;
const uint64_t MAX_CSKEW   =  10000000;
const uint64_t MAX_NWDELAY =  15000000;

const int NUM_TASKS = 6;
const int NUM_MCASTS = 1;
const int MSG_SIZE = 8;

const int PORT = 33333;
const char IP_ADDR[_MAX_NUM_TASKS + _MAX_NUM_MCASTS][_IP_LENGTH] =
  { "192.168.1.1",
    "192.168.2.1",
    "192.168.2.2",
    "192.168.3.1",
    "192.168.3.2",
    "192.168.3.3",
    "238.0.0.1",
  };

const char MCAST_MEMBER[_MAX_NUM_MCASTS][_MAX_NUM_TASKS] =
  {
    { 0, 1, 1, 0, 0, 0 },
  };
