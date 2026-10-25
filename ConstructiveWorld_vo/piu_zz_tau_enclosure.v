(* piu_zz_tau_enclosure.v — consumer 六片链末棒四片机械拆分（KB10 影子链候选案）第 4/4 片（链末棒·保留原模块名）·真依赖图波 3。
   使命：承载带样点（piu_zz_up_ok/lo_ok×6＋piu_zz_band×4）与审计段（Print Assumptions×3＋Extraction×1）
   （原 δ+ε 区 L3194-3275），闭合 τ 面数值链。
   依赖：Require Export head＋phi1024＋literals（工单零漂移不变式：旧导入路径传递覆盖全部具名——
   head 自带 bank4 伞 Export，α/β/γ/δ/ε 五区名与 bank1..4/base 全达）；自身用 literals 九名
   （qpow_u/l×6、zzL×3）与 base 面定理（tau_face/low_face/wq_pos）、piu_zz_up_ok/lo_ok/band 定义；
   piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   真图证据：对 head/phi1024 名 grep 零语义命中（Export×3 为界面保持要求，非语义依赖）。
   对标：piu_zz_tau_enclosure 原单件（六片链末棒再拆，语句面逐字节等价）。
   构造性：本片语句零假设、零公理。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_enclosure.v *)
Require Export piu_zz_tau_enclosure_head.
Require Export piu_zz_tau_enclosure_phi1024_slim.
Require Export piu_zz_tau_enclosure_literals.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Lemma piu_zz_up_ok_256 : piu_zz_up_ok 256 = false.
Proof.
  unfold piu_zz_up_ok.
  rewrite piu_zz_qpow_u_256, piu_zz_zzL_256.
  vm_compute. reflexivity.
Qed.

Lemma piu_zz_lo_ok_256 : piu_zz_lo_ok 256 = true.
Proof.
  unfold piu_zz_lo_ok.
  rewrite piu_zz_qpow_l_256, piu_zz_zzL_256.
  vm_compute. reflexivity.
Qed.

Lemma piu_zz_up_ok_512 : piu_zz_up_ok 512 = false.
Proof.
  unfold piu_zz_up_ok.
  rewrite piu_zz_qpow_u_512, piu_zz_zzL_512.
  vm_compute. reflexivity.
Qed.

Lemma piu_zz_lo_ok_512 : piu_zz_lo_ok 512 = true.
Proof.
  unfold piu_zz_lo_ok.
  rewrite piu_zz_qpow_l_512, piu_zz_zzL_512.
  vm_compute. reflexivity.
Qed.

Lemma piu_zz_up_ok_1024 : piu_zz_up_ok 1024 = false.
Proof.
  unfold piu_zz_up_ok.
  rewrite piu_zz_qpow_u_1024, piu_zz_zzL_1024.
  vm_compute. reflexivity.
Qed.

Lemma piu_zz_lo_ok_1024 : piu_zz_lo_ok 1024 = true.
Proof.
  unfold piu_zz_lo_ok.
  rewrite piu_zz_qpow_l_1024, piu_zz_zzL_1024.
  vm_compute. reflexivity.
Qed.


Lemma piu_zz_band_up :
  map piu_zz_up_ok (4 :: 8 :: 16 :: 32 :: 64 :: 128 :: nil)%nat
  = (true :: false :: false :: false :: true :: false :: nil)%bool.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_band_lo :
  map piu_zz_lo_ok (4 :: 8 :: 16 :: 32 :: 64 :: 128 :: nil)%nat
  = (false :: true :: true :: true :: true :: true :: nil)%bool.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_band_up_ext :
  map piu_zz_up_ok (256 :: 512 :: 1024 :: nil)%nat
  = (false :: false :: false :: nil)%bool.
Proof.
  cbn [map].
  rewrite piu_zz_up_ok_256, piu_zz_up_ok_512, piu_zz_up_ok_1024.
  reflexivity.
Qed.

Lemma piu_zz_band_lo_ext :
  map piu_zz_lo_ok (256 :: 512 :: 1024 :: nil)%nat
  = (true :: true :: true :: nil)%bool.
Proof.
  cbn [map].
  rewrite piu_zz_lo_ok_256, piu_zz_lo_ok_512, piu_zz_lo_ok_1024.
  reflexivity.
Qed.


(* ================================================================== *)
(* 审计段：Print Assumptions 四关之 G4 + 数据级提取验证（G3）            *)
(* ================================================================== *)

Print Assumptions piu_zz_tau_face.
Print Assumptions piu_zz_low_face.
Print Assumptions piu_zz_wq_pos.

Extraction "piu_zz_tau_enclosure.ml" piu_zz_up_ok piu_zz_lo_ok.

