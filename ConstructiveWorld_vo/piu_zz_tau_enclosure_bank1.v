(* piu_zz_tau_enclosure_bank1.v — piu_zz_tau_enclosure 模块分解第 1 段（共四段）。
   使命：zz_in_Pn 逐点判定表第 513–1024 条（piu_zz_inPn_512_513 … piu_zz_inPn_512_1024），供 zz_Phi 字面值链
   逐点引用；每条引理由 unfold 后单点计算或最小素因子试除见证自证。
   依赖：piu_zz_tau_enclosure_base（前置链）、piu_zz_poincare_engine
   （zz_in_Pn/zz_primeb）、piu_zz_padic_clearing、
   Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure 原单件（ 六 片 split, statements byte-equivalent).
   构造性：全部语句为 bool 等式，闭式自证，零假设、零公理。
   编译配方: coqc -native-compiler no -q -Q . "" piu_zz_tau_enclosure_bank1.v *)
Require Export piu_zz_tau_enclosure_base.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Lemma piu_zz_inPn_512_513 : zz_in_Pn 512 513 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 513)) (2 * 513)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_514 : zz_in_Pn 512 514 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 514)) (2 * 514)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_515 : zz_in_Pn 512 515 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 515)) (2 * 515)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_516 : zz_in_Pn 512 516 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 516)) (2 * 516)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_517 : zz_in_Pn 512 517 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 517)) (2 * 517)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_518 : zz_in_Pn 512 518 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 518)) (2 * 518)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_519 : zz_in_Pn 512 519 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 519)) (2 * 519)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_520 : zz_in_Pn 512 520 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 520)) (2 * 520)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_521 : zz_in_Pn 512 521 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 521)) (2 * 521)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_522 : zz_in_Pn 512 522 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 522)) (2 * 522)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_523 : zz_in_Pn 512 523 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 523)) (2 * 523)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_524 : zz_in_Pn 512 524 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 524)) (2 * 524)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_525 : zz_in_Pn 512 525 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 525)) (2 * 525)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_526 : zz_in_Pn 512 526 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 526)) (2 * 526)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_527 : zz_in_Pn 512 527 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 527)) (2 * 527)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_528 : zz_in_Pn 512 528 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 528)) (2 * 528)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_529 : zz_in_Pn 512 529 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 529)) (2 * 529)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_530 : zz_in_Pn 512 530 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 530)) (2 * 530)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_531 : zz_in_Pn 512 531 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 531)) (2 * 531)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_532 : zz_in_Pn 512 532 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 532)) (2 * 532)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_533 : zz_in_Pn 512 533 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 533)) (2 * 533)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_534 : zz_in_Pn 512 534 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 534)) (2 * 534)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_535 : zz_in_Pn 512 535 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 535)) (2 * 535)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_536 : zz_in_Pn 512 536 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 536)) (2 * 536)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_537 : zz_in_Pn 512 537 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 537)) (2 * 537)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_538 : zz_in_Pn 512 538 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 538)) (2 * 538)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_539 : zz_in_Pn 512 539 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 539)) (2 * 539)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_540 : zz_in_Pn 512 540 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 540)) (2 * 540)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_541 : zz_in_Pn 512 541 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 541)) (2 * 541)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_542 : zz_in_Pn 512 542 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 542)) (2 * 542)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_543 : zz_in_Pn 512 543 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 543)) (2 * 543)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_544 : zz_in_Pn 512 544 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 544)) (2 * 544)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_545 : zz_in_Pn 512 545 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 545)) (2 * 545)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_546 : zz_in_Pn 512 546 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 546)) (2 * 546)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_547 : zz_in_Pn 512 547 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 547)) (2 * 547)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_548 : zz_in_Pn 512 548 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 548)) (2 * 548)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_549 : zz_in_Pn 512 549 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 549)) (2 * 549)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_550 : zz_in_Pn 512 550 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 550)) (2 * 550)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_551 : zz_in_Pn 512 551 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 551)) (2 * 551)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_552 : zz_in_Pn 512 552 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 552)) (2 * 552)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_553 : zz_in_Pn 512 553 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 553)) (2 * 553)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_554 : zz_in_Pn 512 554 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 554)) (2 * 554)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_555 : zz_in_Pn 512 555 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 555)) (2 * 555)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_556 : zz_in_Pn 512 556 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 556)) (2 * 556)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_557 : zz_in_Pn 512 557 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 557)) (2 * 557)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_558 : zz_in_Pn 512 558 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 558)) (2 * 558)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_559 : zz_in_Pn 512 559 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 559)) (2 * 559)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_560 : zz_in_Pn 512 560 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 560)) (2 * 560)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_561 : zz_in_Pn 512 561 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 561)) (2 * 561)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_562 : zz_in_Pn 512 562 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 562)) (2 * 562)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_563 : zz_in_Pn 512 563 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 563)) (2 * 563)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_564 : zz_in_Pn 512 564 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 564)) (2 * 564)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_565 : zz_in_Pn 512 565 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 565)) (2 * 565)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_566 : zz_in_Pn 512 566 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 566)) (2 * 566)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_567 : zz_in_Pn 512 567 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 567)) (2 * 567)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_568 : zz_in_Pn 512 568 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 568)) (2 * 568)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_569 : zz_in_Pn 512 569 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 569)) (2 * 569)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_570 : zz_in_Pn 512 570 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 570)) (2 * 570)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_571 : zz_in_Pn 512 571 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 571)) (2 * 571)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_572 : zz_in_Pn 512 572 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 572)) (2 * 572)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_573 : zz_in_Pn 512 573 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 573)) (2 * 573)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_574 : zz_in_Pn 512 574 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 574)) (2 * 574)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_575 : zz_in_Pn 512 575 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 575)) (2 * 575)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_576 : zz_in_Pn 512 576 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 576)) (2 * 576)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_577 : zz_in_Pn 512 577 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 577)) (2 * 577)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_578 : zz_in_Pn 512 578 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 578)) (2 * 578)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_579 : zz_in_Pn 512 579 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 579)) (2 * 579)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_580 : zz_in_Pn 512 580 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 580)) (2 * 580)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_581 : zz_in_Pn 512 581 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 581)) (2 * 581)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_582 : zz_in_Pn 512 582 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 582)) (2 * 582)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_583 : zz_in_Pn 512 583 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 583)) (2 * 583)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_584 : zz_in_Pn 512 584 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 584)) (2 * 584)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_585 : zz_in_Pn 512 585 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 585)) (2 * 585)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_586 : zz_in_Pn 512 586 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 586)) (2 * 586)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_587 : zz_in_Pn 512 587 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 587)) (2 * 587)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_588 : zz_in_Pn 512 588 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 588)) (2 * 588)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_589 : zz_in_Pn 512 589 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 589)) (2 * 589)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_590 : zz_in_Pn 512 590 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 590)) (2 * 590)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_591 : zz_in_Pn 512 591 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 591)) (2 * 591)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_592 : zz_in_Pn 512 592 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 592)) (2 * 592)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_593 : zz_in_Pn 512 593 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 593)) (2 * 593)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_594 : zz_in_Pn 512 594 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 594)) (2 * 594)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_595 : zz_in_Pn 512 595 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 595)) (2 * 595)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_596 : zz_in_Pn 512 596 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 596)) (2 * 596)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_597 : zz_in_Pn 512 597 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 597)) (2 * 597)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_598 : zz_in_Pn 512 598 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 598)) (2 * 598)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_599 : zz_in_Pn 512 599 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 599)) (2 * 599)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_600 : zz_in_Pn 512 600 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 600)) (2 * 600)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_601 : zz_in_Pn 512 601 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 601)) (2 * 601)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_602 : zz_in_Pn 512 602 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 602)) (2 * 602)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_603 : zz_in_Pn 512 603 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 603)) (2 * 603)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_604 : zz_in_Pn 512 604 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 604)) (2 * 604)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_605 : zz_in_Pn 512 605 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 605)) (2 * 605)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_606 : zz_in_Pn 512 606 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 606)) (2 * 606)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_607 : zz_in_Pn 512 607 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 607)) (2 * 607)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_608 : zz_in_Pn 512 608 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 608)) (2 * 608)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_609 : zz_in_Pn 512 609 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 609)) (2 * 609)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_610 : zz_in_Pn 512 610 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 610)) (2 * 610)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_611 : zz_in_Pn 512 611 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 611)) (2 * 611)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_612 : zz_in_Pn 512 612 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 612)) (2 * 612)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_613 : zz_in_Pn 512 613 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 613)) (2 * 613)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_614 : zz_in_Pn 512 614 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 614)) (2 * 614)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_615 : zz_in_Pn 512 615 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 615)) (2 * 615)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_616 : zz_in_Pn 512 616 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 616)) (2 * 616)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_617 : zz_in_Pn 512 617 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 617)) (2 * 617)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_618 : zz_in_Pn 512 618 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 618)) (2 * 618)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_619 : zz_in_Pn 512 619 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 619)) (2 * 619)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_620 : zz_in_Pn 512 620 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 620)) (2 * 620)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_621 : zz_in_Pn 512 621 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 621)) (2 * 621)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_622 : zz_in_Pn 512 622 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 622)) (2 * 622)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_623 : zz_in_Pn 512 623 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 623)) (2 * 623)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_624 : zz_in_Pn 512 624 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 624)) (2 * 624)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_625 : zz_in_Pn 512 625 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 625)) (2 * 625)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_626 : zz_in_Pn 512 626 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 626)) (2 * 626)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_627 : zz_in_Pn 512 627 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 627)) (2 * 627)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_628 : zz_in_Pn 512 628 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 628)) (2 * 628)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_629 : zz_in_Pn 512 629 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 629)) (2 * 629)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_630 : zz_in_Pn 512 630 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 630)) (2 * 630)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_631 : zz_in_Pn 512 631 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 631)) (2 * 631)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_632 : zz_in_Pn 512 632 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 632)) (2 * 632)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_633 : zz_in_Pn 512 633 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 633)) (2 * 633)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_634 : zz_in_Pn 512 634 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 634)) (2 * 634)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_635 : zz_in_Pn 512 635 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 635)) (2 * 635)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_636 : zz_in_Pn 512 636 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 636)) (2 * 636)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_637 : zz_in_Pn 512 637 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 637)) (2 * 637)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_638 : zz_in_Pn 512 638 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 638)) (2 * 638)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_639 : zz_in_Pn 512 639 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 639)) (2 * 639)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_640 : zz_in_Pn 512 640 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 640)) (2 * 640)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_641 : zz_in_Pn 512 641 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 641)) (2 * 641)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_642 : zz_in_Pn 512 642 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 642)) (2 * 642)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_643 : zz_in_Pn 512 643 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 643)) (2 * 643)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_644 : zz_in_Pn 512 644 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 644)) (2 * 644)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_645 : zz_in_Pn 512 645 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 645)) (2 * 645)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_646 : zz_in_Pn 512 646 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 646)) (2 * 646)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_647 : zz_in_Pn 512 647 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 647)) (2 * 647)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_648 : zz_in_Pn 512 648 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 648)) (2 * 648)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_649 : zz_in_Pn 512 649 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 649)) (2 * 649)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_650 : zz_in_Pn 512 650 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 650)) (2 * 650)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_651 : zz_in_Pn 512 651 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 651)) (2 * 651)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_652 : zz_in_Pn 512 652 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 652)) (2 * 652)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_653 : zz_in_Pn 512 653 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 653)) (2 * 653)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_654 : zz_in_Pn 512 654 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 654)) (2 * 654)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_655 : zz_in_Pn 512 655 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 655)) (2 * 655)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_656 : zz_in_Pn 512 656 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 656)) (2 * 656)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_657 : zz_in_Pn 512 657 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 657)) (2 * 657)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_658 : zz_in_Pn 512 658 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 658)) (2 * 658)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_659 : zz_in_Pn 512 659 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 659)) (2 * 659)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_660 : zz_in_Pn 512 660 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 660)) (2 * 660)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_661 : zz_in_Pn 512 661 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 661)) (2 * 661)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_662 : zz_in_Pn 512 662 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 662)) (2 * 662)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_663 : zz_in_Pn 512 663 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 663)) (2 * 663)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_664 : zz_in_Pn 512 664 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 664)) (2 * 664)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_665 : zz_in_Pn 512 665 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 665)) (2 * 665)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_666 : zz_in_Pn 512 666 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 666)) (2 * 666)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_667 : zz_in_Pn 512 667 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 667)) (2 * 667)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_668 : zz_in_Pn 512 668 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 668)) (2 * 668)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_669 : zz_in_Pn 512 669 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 669)) (2 * 669)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_670 : zz_in_Pn 512 670 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 670)) (2 * 670)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_671 : zz_in_Pn 512 671 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 671)) (2 * 671)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_672 : zz_in_Pn 512 672 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 672)) (2 * 672)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_673 : zz_in_Pn 512 673 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 673)) (2 * 673)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_674 : zz_in_Pn 512 674 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 674)) (2 * 674)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_675 : zz_in_Pn 512 675 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 675)) (2 * 675)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_676 : zz_in_Pn 512 676 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 676)) (2 * 676)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_677 : zz_in_Pn 512 677 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 677)) (2 * 677)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_678 : zz_in_Pn 512 678 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 678)) (2 * 678)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_679 : zz_in_Pn 512 679 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 679)) (2 * 679)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_680 : zz_in_Pn 512 680 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 680)) (2 * 680)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_681 : zz_in_Pn 512 681 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 681)) (2 * 681)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_682 : zz_in_Pn 512 682 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 682)) (2 * 682)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_683 : zz_in_Pn 512 683 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 683)) (2 * 683)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_684 : zz_in_Pn 512 684 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 684)) (2 * 684)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_685 : zz_in_Pn 512 685 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 685)) (2 * 685)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_686 : zz_in_Pn 512 686 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 686)) (2 * 686)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_687 : zz_in_Pn 512 687 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 687)) (2 * 687)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_688 : zz_in_Pn 512 688 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 688)) (2 * 688)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_689 : zz_in_Pn 512 689 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 689)) (2 * 689)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_690 : zz_in_Pn 512 690 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 690)) (2 * 690)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_691 : zz_in_Pn 512 691 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 691)) (2 * 691)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_692 : zz_in_Pn 512 692 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 692)) (2 * 692)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_693 : zz_in_Pn 512 693 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 693)) (2 * 693)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_694 : zz_in_Pn 512 694 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 694)) (2 * 694)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_695 : zz_in_Pn 512 695 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 695)) (2 * 695)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_696 : zz_in_Pn 512 696 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 696)) (2 * 696)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_697 : zz_in_Pn 512 697 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 697)) (2 * 697)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_698 : zz_in_Pn 512 698 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 698)) (2 * 698)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_699 : zz_in_Pn 512 699 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 699)) (2 * 699)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_700 : zz_in_Pn 512 700 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 700)) (2 * 700)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_701 : zz_in_Pn 512 701 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 701)) (2 * 701)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_702 : zz_in_Pn 512 702 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 702)) (2 * 702)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_703 : zz_in_Pn 512 703 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 703)) (2 * 703)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_704 : zz_in_Pn 512 704 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 704)) (2 * 704)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_705 : zz_in_Pn 512 705 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 705)) (2 * 705)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_706 : zz_in_Pn 512 706 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 706)) (2 * 706)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_707 : zz_in_Pn 512 707 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 707)) (2 * 707)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_708 : zz_in_Pn 512 708 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 708)) (2 * 708)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_709 : zz_in_Pn 512 709 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 709)) (2 * 709)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_710 : zz_in_Pn 512 710 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 710)) (2 * 710)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_711 : zz_in_Pn 512 711 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 711)) (2 * 711)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_712 : zz_in_Pn 512 712 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 712)) (2 * 712)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_713 : zz_in_Pn 512 713 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 713)) (2 * 713)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_714 : zz_in_Pn 512 714 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 714)) (2 * 714)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_715 : zz_in_Pn 512 715 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 715)) (2 * 715)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_716 : zz_in_Pn 512 716 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 716)) (2 * 716)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_717 : zz_in_Pn 512 717 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 717)) (2 * 717)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_718 : zz_in_Pn 512 718 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 718)) (2 * 718)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_719 : zz_in_Pn 512 719 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 719)) (2 * 719)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_720 : zz_in_Pn 512 720 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 720)) (2 * 720)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_721 : zz_in_Pn 512 721 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 721)) (2 * 721)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_722 : zz_in_Pn 512 722 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 722)) (2 * 722)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_723 : zz_in_Pn 512 723 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 723)) (2 * 723)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_724 : zz_in_Pn 512 724 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 724)) (2 * 724)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_725 : zz_in_Pn 512 725 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 725)) (2 * 725)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_726 : zz_in_Pn 512 726 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 726)) (2 * 726)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_727 : zz_in_Pn 512 727 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 727)) (2 * 727)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_728 : zz_in_Pn 512 728 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 728)) (2 * 728)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_729 : zz_in_Pn 512 729 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 729)) (2 * 729)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_730 : zz_in_Pn 512 730 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 730)) (2 * 730)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_731 : zz_in_Pn 512 731 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 731)) (2 * 731)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_732 : zz_in_Pn 512 732 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 732)) (2 * 732)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_733 : zz_in_Pn 512 733 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 733)) (2 * 733)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_734 : zz_in_Pn 512 734 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 734)) (2 * 734)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_735 : zz_in_Pn 512 735 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 735)) (2 * 735)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_736 : zz_in_Pn 512 736 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 736)) (2 * 736)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_737 : zz_in_Pn 512 737 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 737)) (2 * 737)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_738 : zz_in_Pn 512 738 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 738)) (2 * 738)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_739 : zz_in_Pn 512 739 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 739)) (2 * 739)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_740 : zz_in_Pn 512 740 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 740)) (2 * 740)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_741 : zz_in_Pn 512 741 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 741)) (2 * 741)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_742 : zz_in_Pn 512 742 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 742)) (2 * 742)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_743 : zz_in_Pn 512 743 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 743)) (2 * 743)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_744 : zz_in_Pn 512 744 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 744)) (2 * 744)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_745 : zz_in_Pn 512 745 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 745)) (2 * 745)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_746 : zz_in_Pn 512 746 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 746)) (2 * 746)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_747 : zz_in_Pn 512 747 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 747)) (2 * 747)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_748 : zz_in_Pn 512 748 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 748)) (2 * 748)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_749 : zz_in_Pn 512 749 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 749)) (2 * 749)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_750 : zz_in_Pn 512 750 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 750)) (2 * 750)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_751 : zz_in_Pn 512 751 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 751)) (2 * 751)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_752 : zz_in_Pn 512 752 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 752)) (2 * 752)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_753 : zz_in_Pn 512 753 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 753)) (2 * 753)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_754 : zz_in_Pn 512 754 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 754)) (2 * 754)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_755 : zz_in_Pn 512 755 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 755)) (2 * 755)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_756 : zz_in_Pn 512 756 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 756)) (2 * 756)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_757 : zz_in_Pn 512 757 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 757)) (2 * 757)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_758 : zz_in_Pn 512 758 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 758)) (2 * 758)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_759 : zz_in_Pn 512 759 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 759)) (2 * 759)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_760 : zz_in_Pn 512 760 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 760)) (2 * 760)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_761 : zz_in_Pn 512 761 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 761)) (2 * 761)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_762 : zz_in_Pn 512 762 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 762)) (2 * 762)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_763 : zz_in_Pn 512 763 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 763)) (2 * 763)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_764 : zz_in_Pn 512 764 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 764)) (2 * 764)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_765 : zz_in_Pn 512 765 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 765)) (2 * 765)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_766 : zz_in_Pn 512 766 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 766)) (2 * 766)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_767 : zz_in_Pn 512 767 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 767)) (2 * 767)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_768 : zz_in_Pn 512 768 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (512 mod 768)) (2 * 768)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_512_769 : zz_in_Pn 512 769 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 769) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_770 : zz_primeb 770 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 770) (770 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_770 : zz_in_Pn 512 770 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_770. reflexivity. Qed.

Lemma piu_zz_primeb_false_771 : zz_primeb 771 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 771) (771 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_771 : zz_in_Pn 512 771 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_771. reflexivity. Qed.

Lemma piu_zz_primeb_false_772 : zz_primeb 772 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 772) (772 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_772 : zz_in_Pn 512 772 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_772. reflexivity. Qed.

Lemma piu_zz_inPn_512_773 : zz_in_Pn 512 773 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 773) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_774 : zz_primeb 774 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 774) (774 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_774 : zz_in_Pn 512 774 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_774. reflexivity. Qed.

Lemma piu_zz_primeb_false_775 : zz_primeb 775 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 775) (775 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_775 : zz_in_Pn 512 775 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_775. reflexivity. Qed.

Lemma piu_zz_primeb_false_776 : zz_primeb 776 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 776) (776 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_776 : zz_in_Pn 512 776 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_776. reflexivity. Qed.

Lemma piu_zz_primeb_false_777 : zz_primeb 777 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 777) (777 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_777 : zz_in_Pn 512 777 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_777. reflexivity. Qed.

Lemma piu_zz_primeb_false_778 : zz_primeb 778 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 778) (778 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_778 : zz_in_Pn 512 778 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_778. reflexivity. Qed.

Lemma piu_zz_primeb_false_779 : zz_primeb 779 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 779) (779 - 1)%nat 19).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_779 : zz_in_Pn 512 779 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_779. reflexivity. Qed.

Lemma piu_zz_primeb_false_780 : zz_primeb 780 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 780) (780 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_780 : zz_in_Pn 512 780 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_780. reflexivity. Qed.

Lemma piu_zz_primeb_false_781 : zz_primeb 781 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 781) (781 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_781 : zz_in_Pn 512 781 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_781. reflexivity. Qed.

Lemma piu_zz_primeb_false_782 : zz_primeb 782 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 782) (782 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_782 : zz_in_Pn 512 782 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_782. reflexivity. Qed.

Lemma piu_zz_primeb_false_783 : zz_primeb 783 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 783) (783 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_783 : zz_in_Pn 512 783 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_783. reflexivity. Qed.

Lemma piu_zz_primeb_false_784 : zz_primeb 784 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 784) (784 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_784 : zz_in_Pn 512 784 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_784. reflexivity. Qed.

Lemma piu_zz_primeb_false_785 : zz_primeb 785 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 785) (785 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_785 : zz_in_Pn 512 785 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_785. reflexivity. Qed.

Lemma piu_zz_primeb_false_786 : zz_primeb 786 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 786) (786 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_786 : zz_in_Pn 512 786 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_786. reflexivity. Qed.

Lemma piu_zz_inPn_512_787 : zz_in_Pn 512 787 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 787) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_788 : zz_primeb 788 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 788) (788 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_788 : zz_in_Pn 512 788 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_788. reflexivity. Qed.

Lemma piu_zz_primeb_false_789 : zz_primeb 789 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 789) (789 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_789 : zz_in_Pn 512 789 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_789. reflexivity. Qed.

Lemma piu_zz_primeb_false_790 : zz_primeb 790 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 790) (790 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_790 : zz_in_Pn 512 790 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_790. reflexivity. Qed.

Lemma piu_zz_primeb_false_791 : zz_primeb 791 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 791) (791 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_791 : zz_in_Pn 512 791 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_791. reflexivity. Qed.

Lemma piu_zz_primeb_false_792 : zz_primeb 792 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 792) (792 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_792 : zz_in_Pn 512 792 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_792. reflexivity. Qed.

Lemma piu_zz_primeb_false_793 : zz_primeb 793 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 793) (793 - 1)%nat 13).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_793 : zz_in_Pn 512 793 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_793. reflexivity. Qed.

Lemma piu_zz_primeb_false_794 : zz_primeb 794 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 794) (794 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_794 : zz_in_Pn 512 794 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_794. reflexivity. Qed.

Lemma piu_zz_primeb_false_795 : zz_primeb 795 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 795) (795 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_795 : zz_in_Pn 512 795 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_795. reflexivity. Qed.

Lemma piu_zz_primeb_false_796 : zz_primeb 796 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 796) (796 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_796 : zz_in_Pn 512 796 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_796. reflexivity. Qed.

Lemma piu_zz_inPn_512_797 : zz_in_Pn 512 797 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 797) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_798 : zz_primeb 798 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 798) (798 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_798 : zz_in_Pn 512 798 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_798. reflexivity. Qed.

Lemma piu_zz_primeb_false_799 : zz_primeb 799 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 799) (799 - 1)%nat 17).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_799 : zz_in_Pn 512 799 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_799. reflexivity. Qed.

Lemma piu_zz_primeb_false_800 : zz_primeb 800 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 800) (800 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_800 : zz_in_Pn 512 800 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_800. reflexivity. Qed.

Lemma piu_zz_primeb_false_801 : zz_primeb 801 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 801) (801 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_801 : zz_in_Pn 512 801 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_801. reflexivity. Qed.

Lemma piu_zz_primeb_false_802 : zz_primeb 802 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 802) (802 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_802 : zz_in_Pn 512 802 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_802. reflexivity. Qed.

Lemma piu_zz_primeb_false_803 : zz_primeb 803 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 803) (803 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_803 : zz_in_Pn 512 803 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_803. reflexivity. Qed.

Lemma piu_zz_primeb_false_804 : zz_primeb 804 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 804) (804 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_804 : zz_in_Pn 512 804 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_804. reflexivity. Qed.

Lemma piu_zz_primeb_false_805 : zz_primeb 805 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 805) (805 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_805 : zz_in_Pn 512 805 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_805. reflexivity. Qed.

Lemma piu_zz_primeb_false_806 : zz_primeb 806 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 806) (806 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_806 : zz_in_Pn 512 806 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_806. reflexivity. Qed.

Lemma piu_zz_primeb_false_807 : zz_primeb 807 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 807) (807 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_807 : zz_in_Pn 512 807 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_807. reflexivity. Qed.

Lemma piu_zz_primeb_false_808 : zz_primeb 808 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 808) (808 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_808 : zz_in_Pn 512 808 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_808. reflexivity. Qed.

Lemma piu_zz_inPn_512_809 : zz_in_Pn 512 809 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 809) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_810 : zz_primeb 810 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 810) (810 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_810 : zz_in_Pn 512 810 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_810. reflexivity. Qed.

Lemma piu_zz_inPn_512_811 : zz_in_Pn 512 811 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 811) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_812 : zz_primeb 812 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 812) (812 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_812 : zz_in_Pn 512 812 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_812. reflexivity. Qed.

Lemma piu_zz_primeb_false_813 : zz_primeb 813 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 813) (813 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_813 : zz_in_Pn 512 813 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_813. reflexivity. Qed.

Lemma piu_zz_primeb_false_814 : zz_primeb 814 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 814) (814 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_814 : zz_in_Pn 512 814 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_814. reflexivity. Qed.

Lemma piu_zz_primeb_false_815 : zz_primeb 815 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 815) (815 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_815 : zz_in_Pn 512 815 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_815. reflexivity. Qed.

Lemma piu_zz_primeb_false_816 : zz_primeb 816 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 816) (816 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_816 : zz_in_Pn 512 816 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_816. reflexivity. Qed.

Lemma piu_zz_primeb_false_817 : zz_primeb 817 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 817) (817 - 1)%nat 19).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_817 : zz_in_Pn 512 817 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_817. reflexivity. Qed.

Lemma piu_zz_primeb_false_818 : zz_primeb 818 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 818) (818 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_818 : zz_in_Pn 512 818 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_818. reflexivity. Qed.

Lemma piu_zz_primeb_false_819 : zz_primeb 819 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 819) (819 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_819 : zz_in_Pn 512 819 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_819. reflexivity. Qed.

Lemma piu_zz_primeb_false_820 : zz_primeb 820 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 820) (820 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_820 : zz_in_Pn 512 820 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_820. reflexivity. Qed.

Lemma piu_zz_inPn_512_821 : zz_in_Pn 512 821 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 821) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_822 : zz_primeb 822 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 822) (822 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_822 : zz_in_Pn 512 822 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_822. reflexivity. Qed.

Lemma piu_zz_inPn_512_823 : zz_in_Pn 512 823 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 823) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_824 : zz_primeb 824 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 824) (824 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_824 : zz_in_Pn 512 824 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_824. reflexivity. Qed.

Lemma piu_zz_primeb_false_825 : zz_primeb 825 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 825) (825 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_825 : zz_in_Pn 512 825 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_825. reflexivity. Qed.

Lemma piu_zz_primeb_false_826 : zz_primeb 826 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 826) (826 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_826 : zz_in_Pn 512 826 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_826. reflexivity. Qed.

Lemma piu_zz_inPn_512_827 : zz_in_Pn 512 827 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 827) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_828 : zz_primeb 828 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 828) (828 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_828 : zz_in_Pn 512 828 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_828. reflexivity. Qed.

Lemma piu_zz_inPn_512_829 : zz_in_Pn 512 829 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 829) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_830 : zz_primeb 830 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 830) (830 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_830 : zz_in_Pn 512 830 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_830. reflexivity. Qed.

Lemma piu_zz_primeb_false_831 : zz_primeb 831 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 831) (831 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_831 : zz_in_Pn 512 831 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_831. reflexivity. Qed.

Lemma piu_zz_primeb_false_832 : zz_primeb 832 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 832) (832 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_832 : zz_in_Pn 512 832 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_832. reflexivity. Qed.

Lemma piu_zz_primeb_false_833 : zz_primeb 833 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 833) (833 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_833 : zz_in_Pn 512 833 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_833. reflexivity. Qed.

Lemma piu_zz_primeb_false_834 : zz_primeb 834 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 834) (834 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_834 : zz_in_Pn 512 834 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_834. reflexivity. Qed.

Lemma piu_zz_primeb_false_835 : zz_primeb 835 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 835) (835 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_835 : zz_in_Pn 512 835 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_835. reflexivity. Qed.

Lemma piu_zz_primeb_false_836 : zz_primeb 836 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 836) (836 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_836 : zz_in_Pn 512 836 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_836. reflexivity. Qed.

Lemma piu_zz_primeb_false_837 : zz_primeb 837 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 837) (837 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_837 : zz_in_Pn 512 837 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_837. reflexivity. Qed.

Lemma piu_zz_primeb_false_838 : zz_primeb 838 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 838) (838 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_838 : zz_in_Pn 512 838 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_838. reflexivity. Qed.

Lemma piu_zz_inPn_512_839 : zz_in_Pn 512 839 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 839) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_840 : zz_primeb 840 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 840) (840 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_840 : zz_in_Pn 512 840 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_840. reflexivity. Qed.

Lemma piu_zz_primeb_false_841 : zz_primeb 841 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 841) (841 - 1)%nat 29).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_841 : zz_in_Pn 512 841 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_841. reflexivity. Qed.

Lemma piu_zz_primeb_false_842 : zz_primeb 842 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 842) (842 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_842 : zz_in_Pn 512 842 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_842. reflexivity. Qed.

Lemma piu_zz_primeb_false_843 : zz_primeb 843 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 843) (843 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_843 : zz_in_Pn 512 843 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_843. reflexivity. Qed.

Lemma piu_zz_primeb_false_844 : zz_primeb 844 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 844) (844 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_844 : zz_in_Pn 512 844 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_844. reflexivity. Qed.

Lemma piu_zz_primeb_false_845 : zz_primeb 845 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 845) (845 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_845 : zz_in_Pn 512 845 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_845. reflexivity. Qed.

Lemma piu_zz_primeb_false_846 : zz_primeb 846 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 846) (846 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_846 : zz_in_Pn 512 846 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_846. reflexivity. Qed.

Lemma piu_zz_primeb_false_847 : zz_primeb 847 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 847) (847 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_847 : zz_in_Pn 512 847 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_847. reflexivity. Qed.

Lemma piu_zz_primeb_false_848 : zz_primeb 848 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 848) (848 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_848 : zz_in_Pn 512 848 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_848. reflexivity. Qed.

Lemma piu_zz_primeb_false_849 : zz_primeb 849 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 849) (849 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_849 : zz_in_Pn 512 849 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_849. reflexivity. Qed.

Lemma piu_zz_primeb_false_850 : zz_primeb 850 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 850) (850 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_850 : zz_in_Pn 512 850 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_850. reflexivity. Qed.

Lemma piu_zz_primeb_false_851 : zz_primeb 851 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 851) (851 - 1)%nat 23).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_851 : zz_in_Pn 512 851 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_851. reflexivity. Qed.

Lemma piu_zz_primeb_false_852 : zz_primeb 852 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 852) (852 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_852 : zz_in_Pn 512 852 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_852. reflexivity. Qed.

Lemma piu_zz_inPn_512_853 : zz_in_Pn 512 853 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 853) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_854 : zz_primeb 854 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 854) (854 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_854 : zz_in_Pn 512 854 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_854. reflexivity. Qed.

Lemma piu_zz_primeb_false_855 : zz_primeb 855 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 855) (855 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_855 : zz_in_Pn 512 855 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_855. reflexivity. Qed.

Lemma piu_zz_primeb_false_856 : zz_primeb 856 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 856) (856 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_856 : zz_in_Pn 512 856 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_856. reflexivity. Qed.

Lemma piu_zz_inPn_512_857 : zz_in_Pn 512 857 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 857) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_858 : zz_primeb 858 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 858) (858 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_858 : zz_in_Pn 512 858 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_858. reflexivity. Qed.

Lemma piu_zz_inPn_512_859 : zz_in_Pn 512 859 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 859) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_860 : zz_primeb 860 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 860) (860 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_860 : zz_in_Pn 512 860 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_860. reflexivity. Qed.

Lemma piu_zz_primeb_false_861 : zz_primeb 861 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 861) (861 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_861 : zz_in_Pn 512 861 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_861. reflexivity. Qed.

Lemma piu_zz_primeb_false_862 : zz_primeb 862 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 862) (862 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_862 : zz_in_Pn 512 862 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_862. reflexivity. Qed.

Lemma piu_zz_inPn_512_863 : zz_in_Pn 512 863 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 863) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_864 : zz_primeb 864 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 864) (864 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_864 : zz_in_Pn 512 864 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_864. reflexivity. Qed.

Lemma piu_zz_primeb_false_865 : zz_primeb 865 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 865) (865 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_865 : zz_in_Pn 512 865 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_865. reflexivity. Qed.

Lemma piu_zz_primeb_false_866 : zz_primeb 866 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 866) (866 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_866 : zz_in_Pn 512 866 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_866. reflexivity. Qed.

Lemma piu_zz_primeb_false_867 : zz_primeb 867 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 867) (867 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_867 : zz_in_Pn 512 867 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_867. reflexivity. Qed.

Lemma piu_zz_primeb_false_868 : zz_primeb 868 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 868) (868 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_868 : zz_in_Pn 512 868 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_868. reflexivity. Qed.

Lemma piu_zz_primeb_false_869 : zz_primeb 869 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 869) (869 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_869 : zz_in_Pn 512 869 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_869. reflexivity. Qed.

Lemma piu_zz_primeb_false_870 : zz_primeb 870 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 870) (870 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_870 : zz_in_Pn 512 870 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_870. reflexivity. Qed.

Lemma piu_zz_primeb_false_871 : zz_primeb 871 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 871) (871 - 1)%nat 13).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_871 : zz_in_Pn 512 871 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_871. reflexivity. Qed.

Lemma piu_zz_primeb_false_872 : zz_primeb 872 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 872) (872 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_872 : zz_in_Pn 512 872 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_872. reflexivity. Qed.

Lemma piu_zz_primeb_false_873 : zz_primeb 873 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 873) (873 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_873 : zz_in_Pn 512 873 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_873. reflexivity. Qed.

Lemma piu_zz_primeb_false_874 : zz_primeb 874 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 874) (874 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_874 : zz_in_Pn 512 874 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_874. reflexivity. Qed.

Lemma piu_zz_primeb_false_875 : zz_primeb 875 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 875) (875 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_875 : zz_in_Pn 512 875 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_875. reflexivity. Qed.

Lemma piu_zz_primeb_false_876 : zz_primeb 876 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 876) (876 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_876 : zz_in_Pn 512 876 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_876. reflexivity. Qed.

Lemma piu_zz_inPn_512_877 : zz_in_Pn 512 877 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 877) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_878 : zz_primeb 878 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 878) (878 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_878 : zz_in_Pn 512 878 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_878. reflexivity. Qed.

Lemma piu_zz_primeb_false_879 : zz_primeb 879 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 879) (879 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_879 : zz_in_Pn 512 879 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_879. reflexivity. Qed.

Lemma piu_zz_primeb_false_880 : zz_primeb 880 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 880) (880 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_880 : zz_in_Pn 512 880 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_880. reflexivity. Qed.

Lemma piu_zz_inPn_512_881 : zz_in_Pn 512 881 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 881) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_882 : zz_primeb 882 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 882) (882 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_882 : zz_in_Pn 512 882 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_882. reflexivity. Qed.

Lemma piu_zz_inPn_512_883 : zz_in_Pn 512 883 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 883) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_884 : zz_primeb 884 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 884) (884 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_884 : zz_in_Pn 512 884 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_884. reflexivity. Qed.

Lemma piu_zz_primeb_false_885 : zz_primeb 885 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 885) (885 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_885 : zz_in_Pn 512 885 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_885. reflexivity. Qed.

Lemma piu_zz_primeb_false_886 : zz_primeb 886 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 886) (886 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_886 : zz_in_Pn 512 886 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_886. reflexivity. Qed.

Lemma piu_zz_inPn_512_887 : zz_in_Pn 512 887 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 887) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_888 : zz_primeb 888 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 888) (888 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_888 : zz_in_Pn 512 888 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_888. reflexivity. Qed.

Lemma piu_zz_primeb_false_889 : zz_primeb 889 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 889) (889 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_889 : zz_in_Pn 512 889 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_889. reflexivity. Qed.

Lemma piu_zz_primeb_false_890 : zz_primeb 890 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 890) (890 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_890 : zz_in_Pn 512 890 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_890. reflexivity. Qed.

Lemma piu_zz_primeb_false_891 : zz_primeb 891 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 891) (891 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_891 : zz_in_Pn 512 891 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_891. reflexivity. Qed.

Lemma piu_zz_primeb_false_892 : zz_primeb 892 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 892) (892 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_892 : zz_in_Pn 512 892 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_892. reflexivity. Qed.

Lemma piu_zz_primeb_false_893 : zz_primeb 893 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 893) (893 - 1)%nat 19).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_893 : zz_in_Pn 512 893 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_893. reflexivity. Qed.

Lemma piu_zz_primeb_false_894 : zz_primeb 894 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 894) (894 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_894 : zz_in_Pn 512 894 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_894. reflexivity. Qed.

Lemma piu_zz_primeb_false_895 : zz_primeb 895 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 895) (895 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_895 : zz_in_Pn 512 895 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_895. reflexivity. Qed.

Lemma piu_zz_primeb_false_896 : zz_primeb 896 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 896) (896 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_896 : zz_in_Pn 512 896 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_896. reflexivity. Qed.

Lemma piu_zz_primeb_false_897 : zz_primeb 897 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 897) (897 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_897 : zz_in_Pn 512 897 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_897. reflexivity. Qed.

Lemma piu_zz_primeb_false_898 : zz_primeb 898 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 898) (898 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_898 : zz_in_Pn 512 898 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_898. reflexivity. Qed.

Lemma piu_zz_primeb_false_899 : zz_primeb 899 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 899) (899 - 1)%nat 29).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_899 : zz_in_Pn 512 899 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_899. reflexivity. Qed.

Lemma piu_zz_primeb_false_900 : zz_primeb 900 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 900) (900 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_900 : zz_in_Pn 512 900 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_900. reflexivity. Qed.

Lemma piu_zz_primeb_false_901 : zz_primeb 901 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 901) (901 - 1)%nat 17).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_901 : zz_in_Pn 512 901 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_901. reflexivity. Qed.

Lemma piu_zz_primeb_false_902 : zz_primeb 902 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 902) (902 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_902 : zz_in_Pn 512 902 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_902. reflexivity. Qed.

Lemma piu_zz_primeb_false_903 : zz_primeb 903 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 903) (903 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_903 : zz_in_Pn 512 903 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_903. reflexivity. Qed.

Lemma piu_zz_primeb_false_904 : zz_primeb 904 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 904) (904 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_904 : zz_in_Pn 512 904 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_904. reflexivity. Qed.

Lemma piu_zz_primeb_false_905 : zz_primeb 905 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 905) (905 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_905 : zz_in_Pn 512 905 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_905. reflexivity. Qed.

Lemma piu_zz_primeb_false_906 : zz_primeb 906 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 906) (906 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_906 : zz_in_Pn 512 906 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_906. reflexivity. Qed.

Lemma piu_zz_inPn_512_907 : zz_in_Pn 512 907 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 907) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_908 : zz_primeb 908 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 908) (908 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_908 : zz_in_Pn 512 908 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_908. reflexivity. Qed.

Lemma piu_zz_primeb_false_909 : zz_primeb 909 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 909) (909 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_909 : zz_in_Pn 512 909 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_909. reflexivity. Qed.

Lemma piu_zz_primeb_false_910 : zz_primeb 910 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 910) (910 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_910 : zz_in_Pn 512 910 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_910. reflexivity. Qed.

Lemma piu_zz_inPn_512_911 : zz_in_Pn 512 911 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 911) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_912 : zz_primeb 912 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 912) (912 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_912 : zz_in_Pn 512 912 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_912. reflexivity. Qed.

Lemma piu_zz_primeb_false_913 : zz_primeb 913 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 913) (913 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_913 : zz_in_Pn 512 913 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_913. reflexivity. Qed.

Lemma piu_zz_primeb_false_914 : zz_primeb 914 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 914) (914 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_914 : zz_in_Pn 512 914 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_914. reflexivity. Qed.

Lemma piu_zz_primeb_false_915 : zz_primeb 915 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 915) (915 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_915 : zz_in_Pn 512 915 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_915. reflexivity. Qed.

Lemma piu_zz_primeb_false_916 : zz_primeb 916 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 916) (916 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_916 : zz_in_Pn 512 916 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_916. reflexivity. Qed.

Lemma piu_zz_primeb_false_917 : zz_primeb 917 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 917) (917 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_917 : zz_in_Pn 512 917 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_917. reflexivity. Qed.

Lemma piu_zz_primeb_false_918 : zz_primeb 918 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 918) (918 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_918 : zz_in_Pn 512 918 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_918. reflexivity. Qed.

Lemma piu_zz_inPn_512_919 : zz_in_Pn 512 919 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 919) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_920 : zz_primeb 920 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 920) (920 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_920 : zz_in_Pn 512 920 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_920. reflexivity. Qed.

Lemma piu_zz_primeb_false_921 : zz_primeb 921 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 921) (921 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_921 : zz_in_Pn 512 921 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_921. reflexivity. Qed.

Lemma piu_zz_primeb_false_922 : zz_primeb 922 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 922) (922 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_922 : zz_in_Pn 512 922 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_922. reflexivity. Qed.

Lemma piu_zz_primeb_false_923 : zz_primeb 923 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 923) (923 - 1)%nat 13).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_923 : zz_in_Pn 512 923 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_923. reflexivity. Qed.

Lemma piu_zz_primeb_false_924 : zz_primeb 924 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 924) (924 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_924 : zz_in_Pn 512 924 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_924. reflexivity. Qed.

Lemma piu_zz_primeb_false_925 : zz_primeb 925 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 925) (925 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_925 : zz_in_Pn 512 925 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_925. reflexivity. Qed.

Lemma piu_zz_primeb_false_926 : zz_primeb 926 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 926) (926 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_926 : zz_in_Pn 512 926 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_926. reflexivity. Qed.

Lemma piu_zz_primeb_false_927 : zz_primeb 927 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 927) (927 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_927 : zz_in_Pn 512 927 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_927. reflexivity. Qed.

Lemma piu_zz_primeb_false_928 : zz_primeb 928 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 928) (928 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_928 : zz_in_Pn 512 928 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_928. reflexivity. Qed.

Lemma piu_zz_inPn_512_929 : zz_in_Pn 512 929 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 929) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_930 : zz_primeb 930 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 930) (930 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_930 : zz_in_Pn 512 930 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_930. reflexivity. Qed.

Lemma piu_zz_primeb_false_931 : zz_primeb 931 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 931) (931 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_931 : zz_in_Pn 512 931 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_931. reflexivity. Qed.

Lemma piu_zz_primeb_false_932 : zz_primeb 932 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 932) (932 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_932 : zz_in_Pn 512 932 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_932. reflexivity. Qed.

Lemma piu_zz_primeb_false_933 : zz_primeb 933 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 933) (933 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_933 : zz_in_Pn 512 933 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_933. reflexivity. Qed.

Lemma piu_zz_primeb_false_934 : zz_primeb 934 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 934) (934 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_934 : zz_in_Pn 512 934 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_934. reflexivity. Qed.

Lemma piu_zz_primeb_false_935 : zz_primeb 935 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 935) (935 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_935 : zz_in_Pn 512 935 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_935. reflexivity. Qed.

Lemma piu_zz_primeb_false_936 : zz_primeb 936 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 936) (936 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_936 : zz_in_Pn 512 936 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_936. reflexivity. Qed.

Lemma piu_zz_inPn_512_937 : zz_in_Pn 512 937 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 937) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_938 : zz_primeb 938 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 938) (938 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_938 : zz_in_Pn 512 938 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_938. reflexivity. Qed.

Lemma piu_zz_primeb_false_939 : zz_primeb 939 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 939) (939 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_939 : zz_in_Pn 512 939 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_939. reflexivity. Qed.

Lemma piu_zz_primeb_false_940 : zz_primeb 940 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 940) (940 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_940 : zz_in_Pn 512 940 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_940. reflexivity. Qed.

Lemma piu_zz_inPn_512_941 : zz_in_Pn 512 941 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 941) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_942 : zz_primeb 942 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 942) (942 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_942 : zz_in_Pn 512 942 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_942. reflexivity. Qed.

Lemma piu_zz_primeb_false_943 : zz_primeb 943 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 943) (943 - 1)%nat 23).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_943 : zz_in_Pn 512 943 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_943. reflexivity. Qed.

Lemma piu_zz_primeb_false_944 : zz_primeb 944 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 944) (944 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_944 : zz_in_Pn 512 944 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_944. reflexivity. Qed.

Lemma piu_zz_primeb_false_945 : zz_primeb 945 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 945) (945 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_945 : zz_in_Pn 512 945 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_945. reflexivity. Qed.

Lemma piu_zz_primeb_false_946 : zz_primeb 946 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 946) (946 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_946 : zz_in_Pn 512 946 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_946. reflexivity. Qed.

Lemma piu_zz_inPn_512_947 : zz_in_Pn 512 947 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 947) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_948 : zz_primeb 948 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 948) (948 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_948 : zz_in_Pn 512 948 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_948. reflexivity. Qed.

Lemma piu_zz_primeb_false_949 : zz_primeb 949 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 949) (949 - 1)%nat 13).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_949 : zz_in_Pn 512 949 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_949. reflexivity. Qed.

Lemma piu_zz_primeb_false_950 : zz_primeb 950 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 950) (950 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_950 : zz_in_Pn 512 950 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_950. reflexivity. Qed.

Lemma piu_zz_primeb_false_951 : zz_primeb 951 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 951) (951 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_951 : zz_in_Pn 512 951 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_951. reflexivity. Qed.

Lemma piu_zz_primeb_false_952 : zz_primeb 952 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 952) (952 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_952 : zz_in_Pn 512 952 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_952. reflexivity. Qed.

Lemma piu_zz_inPn_512_953 : zz_in_Pn 512 953 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 953) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_954 : zz_primeb 954 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 954) (954 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_954 : zz_in_Pn 512 954 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_954. reflexivity. Qed.

Lemma piu_zz_primeb_false_955 : zz_primeb 955 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 955) (955 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_955 : zz_in_Pn 512 955 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_955. reflexivity. Qed.

Lemma piu_zz_primeb_false_956 : zz_primeb 956 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 956) (956 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_956 : zz_in_Pn 512 956 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_956. reflexivity. Qed.

Lemma piu_zz_primeb_false_957 : zz_primeb 957 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 957) (957 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_957 : zz_in_Pn 512 957 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_957. reflexivity. Qed.

Lemma piu_zz_primeb_false_958 : zz_primeb 958 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 958) (958 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_958 : zz_in_Pn 512 958 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_958. reflexivity. Qed.

Lemma piu_zz_primeb_false_959 : zz_primeb 959 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 959) (959 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_959 : zz_in_Pn 512 959 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_959. reflexivity. Qed.

Lemma piu_zz_primeb_false_960 : zz_primeb 960 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 960) (960 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_960 : zz_in_Pn 512 960 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_960. reflexivity. Qed.

Lemma piu_zz_primeb_false_961 : zz_primeb 961 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 961) (961 - 1)%nat 31).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_961 : zz_in_Pn 512 961 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_961. reflexivity. Qed.

Lemma piu_zz_primeb_false_962 : zz_primeb 962 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 962) (962 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_962 : zz_in_Pn 512 962 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_962. reflexivity. Qed.

Lemma piu_zz_primeb_false_963 : zz_primeb 963 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 963) (963 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_963 : zz_in_Pn 512 963 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_963. reflexivity. Qed.

Lemma piu_zz_primeb_false_964 : zz_primeb 964 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 964) (964 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_964 : zz_in_Pn 512 964 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_964. reflexivity. Qed.

Lemma piu_zz_primeb_false_965 : zz_primeb 965 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 965) (965 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_965 : zz_in_Pn 512 965 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_965. reflexivity. Qed.

Lemma piu_zz_primeb_false_966 : zz_primeb 966 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 966) (966 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_966 : zz_in_Pn 512 966 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_966. reflexivity. Qed.

Lemma piu_zz_inPn_512_967 : zz_in_Pn 512 967 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 967) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_968 : zz_primeb 968 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 968) (968 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_968 : zz_in_Pn 512 968 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_968. reflexivity. Qed.

Lemma piu_zz_primeb_false_969 : zz_primeb 969 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 969) (969 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_969 : zz_in_Pn 512 969 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_969. reflexivity. Qed.

Lemma piu_zz_primeb_false_970 : zz_primeb 970 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 970) (970 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_970 : zz_in_Pn 512 970 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_970. reflexivity. Qed.

Lemma piu_zz_inPn_512_971 : zz_in_Pn 512 971 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 971) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_972 : zz_primeb 972 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 972) (972 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_972 : zz_in_Pn 512 972 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_972. reflexivity. Qed.

Lemma piu_zz_primeb_false_973 : zz_primeb 973 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 973) (973 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_973 : zz_in_Pn 512 973 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_973. reflexivity. Qed.

Lemma piu_zz_primeb_false_974 : zz_primeb 974 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 974) (974 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_974 : zz_in_Pn 512 974 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_974. reflexivity. Qed.

Lemma piu_zz_primeb_false_975 : zz_primeb 975 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 975) (975 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_975 : zz_in_Pn 512 975 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_975. reflexivity. Qed.

Lemma piu_zz_primeb_false_976 : zz_primeb 976 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 976) (976 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_976 : zz_in_Pn 512 976 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_976. reflexivity. Qed.

Lemma piu_zz_inPn_512_977 : zz_in_Pn 512 977 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 977) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_978 : zz_primeb 978 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 978) (978 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_978 : zz_in_Pn 512 978 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_978. reflexivity. Qed.

Lemma piu_zz_primeb_false_979 : zz_primeb 979 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 979) (979 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_979 : zz_in_Pn 512 979 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_979. reflexivity. Qed.

Lemma piu_zz_primeb_false_980 : zz_primeb 980 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 980) (980 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_980 : zz_in_Pn 512 980 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_980. reflexivity. Qed.

Lemma piu_zz_primeb_false_981 : zz_primeb 981 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 981) (981 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_981 : zz_in_Pn 512 981 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_981. reflexivity. Qed.

Lemma piu_zz_primeb_false_982 : zz_primeb 982 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 982) (982 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_982 : zz_in_Pn 512 982 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_982. reflexivity. Qed.

Lemma piu_zz_inPn_512_983 : zz_in_Pn 512 983 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 983) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_984 : zz_primeb 984 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 984) (984 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_984 : zz_in_Pn 512 984 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_984. reflexivity. Qed.

Lemma piu_zz_primeb_false_985 : zz_primeb 985 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 985) (985 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_985 : zz_in_Pn 512 985 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_985. reflexivity. Qed.

Lemma piu_zz_primeb_false_986 : zz_primeb 986 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 986) (986 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_986 : zz_in_Pn 512 986 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_986. reflexivity. Qed.

Lemma piu_zz_primeb_false_987 : zz_primeb 987 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 987) (987 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_987 : zz_in_Pn 512 987 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_987. reflexivity. Qed.

Lemma piu_zz_primeb_false_988 : zz_primeb 988 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 988) (988 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_988 : zz_in_Pn 512 988 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_988. reflexivity. Qed.

Lemma piu_zz_primeb_false_989 : zz_primeb 989 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 989) (989 - 1)%nat 23).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_989 : zz_in_Pn 512 989 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_989. reflexivity. Qed.

Lemma piu_zz_primeb_false_990 : zz_primeb 990 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 990) (990 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_990 : zz_in_Pn 512 990 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_990. reflexivity. Qed.

Lemma piu_zz_inPn_512_991 : zz_in_Pn 512 991 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 991) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_992 : zz_primeb 992 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 992) (992 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_992 : zz_in_Pn 512 992 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_992. reflexivity. Qed.

Lemma piu_zz_primeb_false_993 : zz_primeb 993 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 993) (993 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_993 : zz_in_Pn 512 993 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_993. reflexivity. Qed.

Lemma piu_zz_primeb_false_994 : zz_primeb 994 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 994) (994 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_994 : zz_in_Pn 512 994 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_994. reflexivity. Qed.

Lemma piu_zz_primeb_false_995 : zz_primeb 995 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 995) (995 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_995 : zz_in_Pn 512 995 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_995. reflexivity. Qed.

Lemma piu_zz_primeb_false_996 : zz_primeb 996 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 996) (996 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_996 : zz_in_Pn 512 996 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_996. reflexivity. Qed.

Lemma piu_zz_inPn_512_997 : zz_in_Pn 512 997 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 997) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_998 : zz_primeb 998 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 998) (998 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_998 : zz_in_Pn 512 998 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_998. reflexivity. Qed.

Lemma piu_zz_primeb_false_999 : zz_primeb 999 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 999) (999 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_999 : zz_in_Pn 512 999 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_999. reflexivity. Qed.

Lemma piu_zz_primeb_false_1000 : zz_primeb 1000 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1000) (1000 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1000 : zz_in_Pn 512 1000 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1000. reflexivity. Qed.

Lemma piu_zz_primeb_false_1001 : zz_primeb 1001 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1001) (1001 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1001 : zz_in_Pn 512 1001 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1001. reflexivity. Qed.

Lemma piu_zz_primeb_false_1002 : zz_primeb 1002 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1002) (1002 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1002 : zz_in_Pn 512 1002 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1002. reflexivity. Qed.

Lemma piu_zz_primeb_false_1003 : zz_primeb 1003 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1003) (1003 - 1)%nat 17).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1003 : zz_in_Pn 512 1003 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1003. reflexivity. Qed.

Lemma piu_zz_primeb_false_1004 : zz_primeb 1004 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1004) (1004 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1004 : zz_in_Pn 512 1004 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1004. reflexivity. Qed.

Lemma piu_zz_primeb_false_1005 : zz_primeb 1005 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1005) (1005 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1005 : zz_in_Pn 512 1005 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1005. reflexivity. Qed.

Lemma piu_zz_primeb_false_1006 : zz_primeb 1006 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1006) (1006 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1006 : zz_in_Pn 512 1006 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1006. reflexivity. Qed.

Lemma piu_zz_primeb_false_1007 : zz_primeb 1007 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1007) (1007 - 1)%nat 19).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1007 : zz_in_Pn 512 1007 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1007. reflexivity. Qed.

Lemma piu_zz_primeb_false_1008 : zz_primeb 1008 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1008) (1008 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1008 : zz_in_Pn 512 1008 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1008. reflexivity. Qed.

Lemma piu_zz_inPn_512_1009 : zz_in_Pn 512 1009 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 1009) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_1010 : zz_primeb 1010 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1010) (1010 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1010 : zz_in_Pn 512 1010 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1010. reflexivity. Qed.

Lemma piu_zz_primeb_false_1011 : zz_primeb 1011 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1011) (1011 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1011 : zz_in_Pn 512 1011 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1011. reflexivity. Qed.

Lemma piu_zz_primeb_false_1012 : zz_primeb 1012 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1012) (1012 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1012 : zz_in_Pn 512 1012 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1012. reflexivity. Qed.

Lemma piu_zz_inPn_512_1013 : zz_in_Pn 512 1013 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 1013) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_1014 : zz_primeb 1014 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1014) (1014 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1014 : zz_in_Pn 512 1014 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1014. reflexivity. Qed.

Lemma piu_zz_primeb_false_1015 : zz_primeb 1015 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1015) (1015 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1015 : zz_in_Pn 512 1015 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1015. reflexivity. Qed.

Lemma piu_zz_primeb_false_1016 : zz_primeb 1016 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1016) (1016 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1016 : zz_in_Pn 512 1016 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1016. reflexivity. Qed.

Lemma piu_zz_primeb_false_1017 : zz_primeb 1017 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1017) (1017 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1017 : zz_in_Pn 512 1017 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1017. reflexivity. Qed.

Lemma piu_zz_primeb_false_1018 : zz_primeb 1018 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1018) (1018 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1018 : zz_in_Pn 512 1018 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1018. reflexivity. Qed.

Lemma piu_zz_inPn_512_1019 : zz_in_Pn 512 1019 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 1019) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_1020 : zz_primeb 1020 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1020) (1020 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1020 : zz_in_Pn 512 1020 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1020. reflexivity. Qed.

Lemma piu_zz_inPn_512_1021 : zz_in_Pn 512 1021 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 1021) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_1022 : zz_primeb 1022 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1022) (1022 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1022 : zz_in_Pn 512 1022 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1022. reflexivity. Qed.

Lemma piu_zz_primeb_false_1023 : zz_primeb 1023 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1023) (1023 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1023 : zz_in_Pn 512 1023 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1023. reflexivity. Qed.

Lemma piu_zz_primeb_false_1024 : zz_primeb 1024 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 1024) (1024 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_512_1024 : zz_in_Pn 512 1024 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_1024. reflexivity. Qed.

