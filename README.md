# Verification_Digital_Systems

LABORATORY EXERCISES:

Lab 1 - Logic Equivalence Checking (LEC)

LEC is an important part of the front end design verification flow, because synthesis often optimizes 
the design to meet constraints, and there may be manual changes to the synthesized logic for testability, 
power and performance. These processes may change the logic inadvertently. The goal of this lab will be 
to check the logical equivalence between a RTL module and its synthesized version, and remove any logic bugs. 
Conformal LEC from Cadence will be used for this lab.

Lab 2 - Assertion Based Verification (ABV)

Assertion based verification is a methodology in which designers use assertions to capture specific design 
intent and, either through simulation, formal verification, or emulation of these assertions, verify that 
the design correctly implements that intent. In this lab, assertions must be added to a testbench to check 
for the correct operation of a protocol during simulation of the design. Mentor Questa will be the simulator 
used for this purpose.

Lab 3 - Universal Verification Methodology (UVM)

Universal Verification Methodology (UVM) is a powerful standardized verification methodology that was 
architected to be able to verify a wide range of design sizes and design types. In this lab, a UVM testbench 
will be set up in SystemVerilog for the given design under test (DUT). Using constrained random verification, 
the design will be tested for functional bugs. Mentor Questa will again be used for this lab.

Lab 4 - Formal Verification

This lab is designed to use a formal verification tool, JasperGold from Cadence, to check specified properties 
for all possible states of the design. An important takeaway from this lab is the ease with which properties 
could cause the tool to give vacuous results, take a very long time to complete the analysis, or time out, unless 
the specified properties are representative of the real design intent. Some recent advances in exposing subtle 
bugs in a complex design will also be studied.
