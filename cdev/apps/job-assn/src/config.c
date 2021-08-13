#include "app.h"
#include <stdint.h>

const uint64_t PALS_PERIOD = 1000000000;
const uint64_t MAX_CSKEW   =  10000000;
const uint64_t MAX_NWDELAY =  15000000;

const int NUM_TASKS = 9;
const int NUM_MCASTS = 1;
const int MSG_SIZE = 2;

const int PORT = 33333;
const char IP_ADDR[_MAX_NUM_TASKS + _MAX_NUM_MCASTS][_IP_LENGTH] =
  { "192.168.1.1",
    "192.168.2.1",
    "192.168.2.2",
    "192.168.2.3",
    "192.168.2.4",
    "192.168.2.5",
    "192.168.2.6",
    "192.168.2.7",
    "192.168.2.8",
    "238.0.0.1",
  };

const char MCAST_MEMBER[_MAX_NUM_MCASTS][_MAX_NUM_TASKS] =
  {
    { 1, 1, 1, 1, 1, 1, 1, 1, 1 },
  };
