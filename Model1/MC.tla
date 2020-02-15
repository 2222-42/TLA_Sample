---- MODULE MC ----
EXTENDS main3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_158177100177436000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_158177100177437000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_158177100177438000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Feb 15 21:50:01 JST 2020 by daioh
