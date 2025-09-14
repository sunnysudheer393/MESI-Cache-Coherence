package mesi_types;
typedef enum logic[1:0] { Invalid = 2'b00, Shared = 2'b01, Exclusive = 2'b10, Modified = 2'b11  } cache_state;

typedef enum logic[1:0] { No_OP = 2'b00, BusRd = 2'b01, BusRdX = 2'b10, BusUpgr = 2'b11 } bus_request;

endpackage