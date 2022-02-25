(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory Systems imports
  System_F1 \<comment> \<open>Frege\<close>
  System_H1 \<comment> \<open>Hilbert\<close>
  System_L0 \<comment> \<open>Lukasiewicz Variant\<close>
  System_L1 \<comment> \<open>Lukasiewicz 1\<close>
  System_L2 \<comment> \<open>Lukasiewicz 2\<close>
  System_L3 \<comment> \<open>Lukasiewicz 3\<close>
  System_M0 \<comment> \<open>Mendelson Variant\<close>
  System_M1 \<comment> \<open>Mendelson\<close>
  System_R1 \<comment> \<open>Russell\<close>
  System_S0 \<comment> \<open>Sobocinski Variant\<close>
  System_S1 \<comment> \<open>Sobocinski 1\<close>
  System_S2 \<comment> \<open>Sobocinski 2\<close>
begin

welcome

thm F1 H1 L0 L1 L2 L3 M0 M1 R1 S0 S1 S2

end
