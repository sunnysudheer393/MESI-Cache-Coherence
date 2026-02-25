##### MESI Cache Coherence Protocol & Formal Verification
## Overview
This repository contains a SystemVerilog implementation of a two-core cache system using the MESI (Modified, Exclusive, Shared, Invalid) protocol, accompanied by a complete Formal Verification (FV) environment. The project models the cache controllers, a shared bus with arbitration, and uses rigorous SystemVerilog Assertions (SVA) to mathematically prove the correctness of the coherence protocol.

## Project Structure
mesi_types.svh: Defines the fundamental enumerations for the cache states (Invalid, Shared, Exclusive, Modified) and bus requests (No_OP, BusRd, BusRdX, BusUpgr).

bus.svh: Implements a sequential bus arbiter that manages requests from the two caches, giving priority to Cache 0 over Cache 1.

cache_mem.svh: The core cache controller logic. It handles CPU reads and writes, issues necessary bus commands (like BusRd, BusRdX, and BusUpgr), and implements snooping logic to react to the other cache's bus activities.

cache_top.svh: The top-level design module that instantiates and connects two cache modules (cache_0 and cache_1) to the shared bus (shared_bus).

cache_tb.svh: A dynamic simulation testbench that generates randomized clock stimulus, CPU reads, CPU writes, and addresses to thoroughly exercise the system.

mesi_assertions.svh: Contains the formal verification testbench (mesi_fv_tb). It uses SystemVerilog Assertions (SVA) assume, assert, and cover properties to prove the protocol's rules are never violated.

mesi_bind.svh: Uses the SystemVerilog bind construct to attach the SVA properties (mesi_fv_tb) directly into the cache_top module without altering the underlying design code.

mesi_formal.tcl: A TCL script that automates the formal verification process. It compiles the files, sets up the clocks/resets, and commands the tool to formally prove all SVA properties.

## Understanding the Formal Verification
Formal verification differs from standard simulation. Instead of running specific test cases, formal tools mathematically analyze the code to guarantee that certain conditions are always or never met under any possible scenario.

In this repository, formal verification guarantees the structural and behavioral correctness of the MESI implementation. Key properties proven include:

# Mutual Exclusion:
Ensures that no two caches can simultaneously be in the Modified or Exclusive state for the exact same address.

# Coherence Guarantee: 
Asserts that if one cache holds a line in the Modified or Exclusive state, the other cache must strictly be in the Invalid state for that same address.

# Valid State Transitions: 
Proves that the cache state machine transitions correctly. For example, transitioning from Shared to Invalid when a BusRdX or BusUpgr snoop hit is detected, or moving from Exclusive to Shared on a BusRd.

# Liveness & Forward Progress: 
Uses assertions to guarantee that if a cache controller requests the bus, it is eventually granted ownership by the arbiter.

# Signal Stability: 
Verifies that requested addresses remain stable while a bus transaction is pending or until the cache has reached a stable state.

### How to Run
## Formal Verification
The repository includes a TCL script to execute the formal verification using standard EDA Formal tools (e.g., Cadence JasperGold or Siemens Questa PropCheck):

Launch your formal verification tool in your terminal.

Source the provided setup script: source mesi_formal.tcl

The tool will compile the SV files, bind the SVA assertions, and attempt to prove all properties while generating structural coverage metrics.

## Simulation Testbench
To run a dynamic simulation:

Compile the design files along with cache_tb.svh in your preferred simulator (e.g., ModelSim, VCS, Verilator).

Run the simulation to observe the randomized CPU read/write stimulus and monitor the resulting bus arbitration and cache state transitions over time.
