---- MODULE MC ----
EXTENDS main3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_158177120258341000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_158177120258342000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_158177120258343000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Feb 15 21:53:22 JST 2020 by daioh
