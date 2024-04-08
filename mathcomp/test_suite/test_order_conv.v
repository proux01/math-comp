From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Section dual_of_dual.
Context (disp : Order.disp_t).

Let eq_dual_dual_porderType (T : porderType disp) :
  Order.POrder.on T = Order.POrder.on T^d^d := erefl.

Let eq_dual_dual_bPOrderType (T : bPOrderType disp) :
  Order.BPOrder.on T = Order.BPOrder.on T^d^d := erefl.

Let eq_dual_dual_tPOrderType (T : tPOrderType disp) :
  Order.TPOrder.on T = Order.TPOrder.on T^d^d := erefl.

Let eq_dual_dual_tbPOrderType (T : tbPOrderType disp) :
  Order.TBPOrder.on T = Order.TBPOrder.on T^d^d := erefl.

Let eq_dual_dual_bLatticeType (T : bLatticeType disp) :
  Order.BLattice.on T = Order.BLattice.on T^d^d := erefl.

Let eq_dual_dual_tLatticeType (T : tLatticeType disp) :
  Order.TLattice.on T = Order.TLattice.on T^d^d := erefl.

Let eq_dual_dual_bDistrLatticeType (T : bDistrLatticeType disp) :
  Order.BDistrLattice.on T = Order.BDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_cbDistrLatticeType (T : cbDistrLatticeType disp) :
  Order.CBDistrLattice.on T = Order.CBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_ctbDistrLatticeType (T : ctbDistrLatticeType disp) :
  Order.CTBDistrLattice.on T = Order.CTBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_finPOrderType (T : finPOrderType disp) :
  Order.FinPOrder.on T = Order.FinPOrder.on T^d^d := erefl.

Let eq_dual_dual_finCDistrLatticeType (T : finCDistrLatticeType disp) :
  Order.FinCDistrLattice.on T = Order.FinCDistrLattice.on T^d^d := erefl.

End dual_of_dual.
