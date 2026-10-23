(* piu_zz_tau_enclosure_bank2.v — piu_zz_tau_enclosure 模块分解第 2 段（共四段）。
   使命：zz_in_Pn 逐点判定表第 1025–1536 条（piu_zz_inPn_1024_513 … piu_zz_inPn_1024_1024），供 zz_Phi 字面值链
   逐点消费；每条引理由 unfold 后单点计算或最小素因子试除见证自证。
   依赖：piu_zz_tau_enclosurepiu_zz_tau_enclosure_bank1（前置链）、piu_zz_poincare_engine
   （zz_in_Pn/zz_primeb）、piu_zz_padic_clearing、
   Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   构造性：全部语句为 bool 等式，闭式自证，零假设、零公理。
   编译配方: coqc -native-compiler no -q -Q . "" piu_zz_tau_enclosure_bank2.v *)
Require Export piu_zz_tau_enclosure_bank1.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Lemma piu_zz_inPn_1024_513 : zz_in_Pn 1024 513 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 513)) (2 * 513)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_514 : zz_in_Pn 1024 514 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 514)) (2 * 514)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_515 : zz_in_Pn 1024 515 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 515)) (2 * 515)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_516 : zz_in_Pn 1024 516 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 516)) (2 * 516)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_517 : zz_in_Pn 1024 517 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 517)) (2 * 517)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_518 : zz_in_Pn 1024 518 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 518)) (2 * 518)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_519 : zz_in_Pn 1024 519 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 519)) (2 * 519)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_520 : zz_in_Pn 1024 520 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 520)) (2 * 520)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_521 : zz_in_Pn 1024 521 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 521)) (2 * 521)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_522 : zz_in_Pn 1024 522 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 522)) (2 * 522)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_523 : zz_in_Pn 1024 523 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 523)) (2 * 523)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_524 : zz_in_Pn 1024 524 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 524)) (2 * 524)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_525 : zz_in_Pn 1024 525 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 525)) (2 * 525)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_526 : zz_in_Pn 1024 526 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 526)) (2 * 526)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_527 : zz_in_Pn 1024 527 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 527)) (2 * 527)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_528 : zz_in_Pn 1024 528 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 528)) (2 * 528)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_529 : zz_in_Pn 1024 529 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 529)) (2 * 529)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_530 : zz_in_Pn 1024 530 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 530)) (2 * 530)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_531 : zz_in_Pn 1024 531 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 531)) (2 * 531)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_532 : zz_in_Pn 1024 532 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 532)) (2 * 532)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_533 : zz_in_Pn 1024 533 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 533)) (2 * 533)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_534 : zz_in_Pn 1024 534 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 534)) (2 * 534)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_535 : zz_in_Pn 1024 535 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 535)) (2 * 535)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_536 : zz_in_Pn 1024 536 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 536)) (2 * 536)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_537 : zz_in_Pn 1024 537 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 537)) (2 * 537)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_538 : zz_in_Pn 1024 538 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 538)) (2 * 538)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_539 : zz_in_Pn 1024 539 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 539)) (2 * 539)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_540 : zz_in_Pn 1024 540 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 540)) (2 * 540)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_541 : zz_in_Pn 1024 541 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 541)) (2 * 541)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_542 : zz_in_Pn 1024 542 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 542)) (2 * 542)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_543 : zz_in_Pn 1024 543 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 543)) (2 * 543)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_544 : zz_in_Pn 1024 544 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 544)) (2 * 544)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_545 : zz_in_Pn 1024 545 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 545)) (2 * 545)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_546 : zz_in_Pn 1024 546 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 546)) (2 * 546)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_547 : zz_in_Pn 1024 547 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 547)) (2 * 547)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_548 : zz_in_Pn 1024 548 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 548)) (2 * 548)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_549 : zz_in_Pn 1024 549 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 549)) (2 * 549)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_550 : zz_in_Pn 1024 550 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 550)) (2 * 550)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_551 : zz_in_Pn 1024 551 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 551)) (2 * 551)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_552 : zz_in_Pn 1024 552 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 552)) (2 * 552)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_553 : zz_in_Pn 1024 553 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 553)) (2 * 553)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_554 : zz_in_Pn 1024 554 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 554)) (2 * 554)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_555 : zz_in_Pn 1024 555 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 555)) (2 * 555)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_556 : zz_in_Pn 1024 556 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 556)) (2 * 556)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_557 : zz_in_Pn 1024 557 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 557)) (2 * 557)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_558 : zz_in_Pn 1024 558 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 558)) (2 * 558)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_559 : zz_in_Pn 1024 559 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 559)) (2 * 559)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_560 : zz_in_Pn 1024 560 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 560)) (2 * 560)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_561 : zz_in_Pn 1024 561 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 561)) (2 * 561)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_562 : zz_in_Pn 1024 562 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 562)) (2 * 562)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_563 : zz_in_Pn 1024 563 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 563)) (2 * 563)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_564 : zz_in_Pn 1024 564 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 564)) (2 * 564)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_565 : zz_in_Pn 1024 565 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 565)) (2 * 565)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_566 : zz_in_Pn 1024 566 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 566)) (2 * 566)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_567 : zz_in_Pn 1024 567 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 567)) (2 * 567)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_568 : zz_in_Pn 1024 568 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 568)) (2 * 568)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_569 : zz_in_Pn 1024 569 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 569)) (2 * 569)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_570 : zz_in_Pn 1024 570 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 570)) (2 * 570)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_571 : zz_in_Pn 1024 571 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 571)) (2 * 571)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_572 : zz_in_Pn 1024 572 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 572)) (2 * 572)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_573 : zz_in_Pn 1024 573 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 573)) (2 * 573)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_574 : zz_in_Pn 1024 574 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 574)) (2 * 574)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_575 : zz_in_Pn 1024 575 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 575)) (2 * 575)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_576 : zz_in_Pn 1024 576 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 576)) (2 * 576)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_577 : zz_in_Pn 1024 577 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 577)) (2 * 577)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_578 : zz_in_Pn 1024 578 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 578)) (2 * 578)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_579 : zz_in_Pn 1024 579 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 579)) (2 * 579)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_580 : zz_in_Pn 1024 580 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 580)) (2 * 580)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_581 : zz_in_Pn 1024 581 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 581)) (2 * 581)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_582 : zz_in_Pn 1024 582 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 582)) (2 * 582)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_583 : zz_in_Pn 1024 583 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 583)) (2 * 583)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_584 : zz_in_Pn 1024 584 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 584)) (2 * 584)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_585 : zz_in_Pn 1024 585 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 585)) (2 * 585)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_586 : zz_in_Pn 1024 586 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 586)) (2 * 586)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_587 : zz_in_Pn 1024 587 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 587)) (2 * 587)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_588 : zz_in_Pn 1024 588 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 588)) (2 * 588)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_589 : zz_in_Pn 1024 589 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 589)) (2 * 589)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_590 : zz_in_Pn 1024 590 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 590)) (2 * 590)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_591 : zz_in_Pn 1024 591 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 591)) (2 * 591)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_592 : zz_in_Pn 1024 592 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 592)) (2 * 592)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_593 : zz_in_Pn 1024 593 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 593)) (2 * 593)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_594 : zz_in_Pn 1024 594 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 594)) (2 * 594)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_595 : zz_in_Pn 1024 595 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 595)) (2 * 595)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_596 : zz_in_Pn 1024 596 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 596)) (2 * 596)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_597 : zz_in_Pn 1024 597 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 597)) (2 * 597)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_598 : zz_in_Pn 1024 598 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 598)) (2 * 598)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_599 : zz_in_Pn 1024 599 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 599)) (2 * 599)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_600 : zz_in_Pn 1024 600 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 600)) (2 * 600)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_601 : zz_in_Pn 1024 601 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 601)) (2 * 601)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_602 : zz_in_Pn 1024 602 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 602)) (2 * 602)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_603 : zz_in_Pn 1024 603 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 603)) (2 * 603)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_604 : zz_in_Pn 1024 604 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 604)) (2 * 604)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_605 : zz_in_Pn 1024 605 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 605)) (2 * 605)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_606 : zz_in_Pn 1024 606 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 606)) (2 * 606)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_607 : zz_in_Pn 1024 607 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 607)) (2 * 607)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_608 : zz_in_Pn 1024 608 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 608)) (2 * 608)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_609 : zz_in_Pn 1024 609 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 609)) (2 * 609)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_610 : zz_in_Pn 1024 610 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 610)) (2 * 610)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_611 : zz_in_Pn 1024 611 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 611)) (2 * 611)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_612 : zz_in_Pn 1024 612 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 612)) (2 * 612)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_613 : zz_in_Pn 1024 613 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 613)) (2 * 613)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_614 : zz_in_Pn 1024 614 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 614)) (2 * 614)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_615 : zz_primeb 615 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 615) (615 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_615 : zz_in_Pn 1024 615 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_615. reflexivity. Qed.

Lemma piu_zz_primeb_false_616 : zz_primeb 616 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 616) (616 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_616 : zz_in_Pn 1024 616 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_616. reflexivity. Qed.

Lemma piu_zz_inPn_1024_617 : zz_in_Pn 1024 617 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 617) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_618 : zz_primeb 618 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 618) (618 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_618 : zz_in_Pn 1024 618 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_618. reflexivity. Qed.

Lemma piu_zz_inPn_1024_619 : zz_in_Pn 1024 619 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 619) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_620 : zz_primeb 620 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 620) (620 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_620 : zz_in_Pn 1024 620 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_620. reflexivity. Qed.

Lemma piu_zz_primeb_false_621 : zz_primeb 621 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 621) (621 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_621 : zz_in_Pn 1024 621 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_621. reflexivity. Qed.

Lemma piu_zz_primeb_false_622 : zz_primeb 622 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 622) (622 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_622 : zz_in_Pn 1024 622 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_622. reflexivity. Qed.

Lemma piu_zz_primeb_false_623 : zz_primeb 623 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 623) (623 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_623 : zz_in_Pn 1024 623 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_623. reflexivity. Qed.

Lemma piu_zz_primeb_false_624 : zz_primeb 624 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 624) (624 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_624 : zz_in_Pn 1024 624 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_624. reflexivity. Qed.

Lemma piu_zz_primeb_false_625 : zz_primeb 625 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 625) (625 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_625 : zz_in_Pn 1024 625 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_625. reflexivity. Qed.

Lemma piu_zz_primeb_false_626 : zz_primeb 626 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 626) (626 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_626 : zz_in_Pn 1024 626 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_626. reflexivity. Qed.

Lemma piu_zz_primeb_false_627 : zz_primeb 627 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 627) (627 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_627 : zz_in_Pn 1024 627 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_627. reflexivity. Qed.

Lemma piu_zz_primeb_false_628 : zz_primeb 628 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 628) (628 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_628 : zz_in_Pn 1024 628 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_628. reflexivity. Qed.

Lemma piu_zz_primeb_false_629 : zz_primeb 629 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 629) (629 - 1)%nat 17).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_629 : zz_in_Pn 1024 629 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_629. reflexivity. Qed.

Lemma piu_zz_primeb_false_630 : zz_primeb 630 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 630) (630 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_630 : zz_in_Pn 1024 630 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_630. reflexivity. Qed.

Lemma piu_zz_inPn_1024_631 : zz_in_Pn 1024 631 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 631) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_632 : zz_primeb 632 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 632) (632 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_632 : zz_in_Pn 1024 632 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_632. reflexivity. Qed.

Lemma piu_zz_primeb_false_633 : zz_primeb 633 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 633) (633 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_633 : zz_in_Pn 1024 633 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_633. reflexivity. Qed.

Lemma piu_zz_primeb_false_634 : zz_primeb 634 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 634) (634 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_634 : zz_in_Pn 1024 634 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_634. reflexivity. Qed.

Lemma piu_zz_primeb_false_635 : zz_primeb 635 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 635) (635 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_635 : zz_in_Pn 1024 635 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_635. reflexivity. Qed.

Lemma piu_zz_primeb_false_636 : zz_primeb 636 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 636) (636 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_636 : zz_in_Pn 1024 636 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_636. reflexivity. Qed.

Lemma piu_zz_primeb_false_637 : zz_primeb 637 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 637) (637 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_637 : zz_in_Pn 1024 637 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_637. reflexivity. Qed.

Lemma piu_zz_primeb_false_638 : zz_primeb 638 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 638) (638 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_638 : zz_in_Pn 1024 638 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_638. reflexivity. Qed.

Lemma piu_zz_primeb_false_639 : zz_primeb 639 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 639) (639 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_639 : zz_in_Pn 1024 639 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_639. reflexivity. Qed.

Lemma piu_zz_primeb_false_640 : zz_primeb 640 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 640) (640 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_640 : zz_in_Pn 1024 640 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_640. reflexivity. Qed.

Lemma piu_zz_inPn_1024_641 : zz_in_Pn 1024 641 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 641) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_642 : zz_primeb 642 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 642) (642 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_642 : zz_in_Pn 1024 642 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_642. reflexivity. Qed.

Lemma piu_zz_inPn_1024_643 : zz_in_Pn 1024 643 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 643) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_644 : zz_primeb 644 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 644) (644 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_644 : zz_in_Pn 1024 644 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_644. reflexivity. Qed.

Lemma piu_zz_primeb_false_645 : zz_primeb 645 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 645) (645 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_645 : zz_in_Pn 1024 645 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_645. reflexivity. Qed.

Lemma piu_zz_primeb_false_646 : zz_primeb 646 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 646) (646 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_646 : zz_in_Pn 1024 646 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_646. reflexivity. Qed.

Lemma piu_zz_inPn_1024_647 : zz_in_Pn 1024 647 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 647) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_648 : zz_primeb 648 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 648) (648 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_648 : zz_in_Pn 1024 648 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_648. reflexivity. Qed.

Lemma piu_zz_primeb_false_649 : zz_primeb 649 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 649) (649 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_649 : zz_in_Pn 1024 649 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_649. reflexivity. Qed.

Lemma piu_zz_primeb_false_650 : zz_primeb 650 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 650) (650 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_650 : zz_in_Pn 1024 650 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_650. reflexivity. Qed.

Lemma piu_zz_primeb_false_651 : zz_primeb 651 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 651) (651 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_651 : zz_in_Pn 1024 651 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_651. reflexivity. Qed.

Lemma piu_zz_primeb_false_652 : zz_primeb 652 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 652) (652 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_652 : zz_in_Pn 1024 652 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_652. reflexivity. Qed.

Lemma piu_zz_inPn_1024_653 : zz_in_Pn 1024 653 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 653) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_654 : zz_primeb 654 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 654) (654 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_654 : zz_in_Pn 1024 654 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_654. reflexivity. Qed.

Lemma piu_zz_primeb_false_655 : zz_primeb 655 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 655) (655 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_655 : zz_in_Pn 1024 655 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_655. reflexivity. Qed.

Lemma piu_zz_primeb_false_656 : zz_primeb 656 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 656) (656 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_656 : zz_in_Pn 1024 656 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_656. reflexivity. Qed.

Lemma piu_zz_primeb_false_657 : zz_primeb 657 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 657) (657 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_657 : zz_in_Pn 1024 657 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_657. reflexivity. Qed.

Lemma piu_zz_primeb_false_658 : zz_primeb 658 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 658) (658 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_658 : zz_in_Pn 1024 658 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_658. reflexivity. Qed.

Lemma piu_zz_inPn_1024_659 : zz_in_Pn 1024 659 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 659) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_660 : zz_primeb 660 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 660) (660 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_660 : zz_in_Pn 1024 660 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_660. reflexivity. Qed.

Lemma piu_zz_inPn_1024_661 : zz_in_Pn 1024 661 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 661) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_662 : zz_primeb 662 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 662) (662 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_662 : zz_in_Pn 1024 662 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_662. reflexivity. Qed.

Lemma piu_zz_primeb_false_663 : zz_primeb 663 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 663) (663 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_663 : zz_in_Pn 1024 663 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_663. reflexivity. Qed.

Lemma piu_zz_primeb_false_664 : zz_primeb 664 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 664) (664 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_664 : zz_in_Pn 1024 664 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_664. reflexivity. Qed.

Lemma piu_zz_primeb_false_665 : zz_primeb 665 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 665) (665 - 1)%nat 5).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_665 : zz_in_Pn 1024 665 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_665. reflexivity. Qed.

Lemma piu_zz_primeb_false_666 : zz_primeb 666 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 666) (666 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_666 : zz_in_Pn 1024 666 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_666. reflexivity. Qed.

Lemma piu_zz_primeb_false_667 : zz_primeb 667 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 667) (667 - 1)%nat 23).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_667 : zz_in_Pn 1024 667 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_667. reflexivity. Qed.

Lemma piu_zz_primeb_false_668 : zz_primeb 668 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 668) (668 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_668 : zz_in_Pn 1024 668 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_668. reflexivity. Qed.

Lemma piu_zz_primeb_false_669 : zz_primeb 669 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 669) (669 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_669 : zz_in_Pn 1024 669 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_669. reflexivity. Qed.

Lemma piu_zz_primeb_false_670 : zz_primeb 670 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 670) (670 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_670 : zz_in_Pn 1024 670 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_670. reflexivity. Qed.

Lemma piu_zz_primeb_false_671 : zz_primeb 671 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 671) (671 - 1)%nat 11).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_671 : zz_in_Pn 1024 671 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_671. reflexivity. Qed.

Lemma piu_zz_primeb_false_672 : zz_primeb 672 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 672) (672 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_672 : zz_in_Pn 1024 672 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_672. reflexivity. Qed.

Lemma piu_zz_inPn_1024_673 : zz_in_Pn 1024 673 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 673) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_674 : zz_primeb 674 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 674) (674 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_674 : zz_in_Pn 1024 674 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_674. reflexivity. Qed.

Lemma piu_zz_primeb_false_675 : zz_primeb 675 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 675) (675 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_675 : zz_in_Pn 1024 675 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_675. reflexivity. Qed.

Lemma piu_zz_primeb_false_676 : zz_primeb 676 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 676) (676 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_676 : zz_in_Pn 1024 676 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_676. reflexivity. Qed.

Lemma piu_zz_inPn_1024_677 : zz_in_Pn 1024 677 = true.
Proof.
  unfold zz_in_Pn.
  replace (zz_primeb 677) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma piu_zz_primeb_false_678 : zz_primeb 678 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 678) (678 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_678 : zz_in_Pn 1024 678 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_678. reflexivity. Qed.

Lemma piu_zz_primeb_false_679 : zz_primeb 679 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 679) (679 - 1)%nat 7).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_679 : zz_in_Pn 1024 679 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_679. reflexivity. Qed.

Lemma piu_zz_primeb_false_680 : zz_primeb 680 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 680) (680 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_680 : zz_in_Pn 1024 680 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_680. reflexivity. Qed.

Lemma piu_zz_primeb_false_681 : zz_primeb 681 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 681) (681 - 1)%nat 3).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_681 : zz_in_Pn 1024 681 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_681. reflexivity. Qed.

Lemma piu_zz_primeb_false_682 : zz_primeb 682 = false.
Proof.
  unfold zz_primeb.
  rewrite (piu_zz_nodiv_upto_hit (Z.of_nat 682) (682 - 1)%nat 2).
  - apply andb_false_r.
  - lia.
  - lia.
  - vm_compute. reflexivity.
Qed.

Lemma piu_zz_inPn_1024_682 : zz_in_Pn 1024 682 = false.
Proof. unfold zz_in_Pn. rewrite piu_zz_primeb_false_682. reflexivity. Qed.

Lemma piu_zz_inPn_1024_683 : zz_in_Pn 1024 683 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 683 (2 * (1024 mod 683))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_684 : zz_in_Pn 1024 684 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 684 (2 * (1024 mod 684))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_685 : zz_in_Pn 1024 685 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 685 (2 * (1024 mod 685))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_686 : zz_in_Pn 1024 686 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 686 (2 * (1024 mod 686))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_687 : zz_in_Pn 1024 687 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 687 (2 * (1024 mod 687))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_688 : zz_in_Pn 1024 688 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 688 (2 * (1024 mod 688))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_689 : zz_in_Pn 1024 689 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 689 (2 * (1024 mod 689))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_690 : zz_in_Pn 1024 690 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 690 (2 * (1024 mod 690))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_691 : zz_in_Pn 1024 691 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 691 (2 * (1024 mod 691))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_692 : zz_in_Pn 1024 692 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 692 (2 * (1024 mod 692))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_693 : zz_in_Pn 1024 693 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 693 (2 * (1024 mod 693))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_694 : zz_in_Pn 1024 694 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 694 (2 * (1024 mod 694))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_695 : zz_in_Pn 1024 695 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 695 (2 * (1024 mod 695))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_696 : zz_in_Pn 1024 696 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 696 (2 * (1024 mod 696))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_697 : zz_in_Pn 1024 697 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 697 (2 * (1024 mod 697))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_698 : zz_in_Pn 1024 698 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 698 (2 * (1024 mod 698))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_699 : zz_in_Pn 1024 699 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 699 (2 * (1024 mod 699))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_700 : zz_in_Pn 1024 700 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 700 (2 * (1024 mod 700))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_701 : zz_in_Pn 1024 701 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 701 (2 * (1024 mod 701))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_702 : zz_in_Pn 1024 702 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 702 (2 * (1024 mod 702))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_703 : zz_in_Pn 1024 703 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 703 (2 * (1024 mod 703))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_704 : zz_in_Pn 1024 704 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 704 (2 * (1024 mod 704))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_705 : zz_in_Pn 1024 705 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 705 (2 * (1024 mod 705))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_706 : zz_in_Pn 1024 706 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 706 (2 * (1024 mod 706))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_707 : zz_in_Pn 1024 707 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 707 (2 * (1024 mod 707))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_708 : zz_in_Pn 1024 708 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 708 (2 * (1024 mod 708))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_709 : zz_in_Pn 1024 709 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 709 (2 * (1024 mod 709))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_710 : zz_in_Pn 1024 710 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 710 (2 * (1024 mod 710))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_711 : zz_in_Pn 1024 711 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 711 (2 * (1024 mod 711))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_712 : zz_in_Pn 1024 712 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 712 (2 * (1024 mod 712))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_713 : zz_in_Pn 1024 713 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 713 (2 * (1024 mod 713))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_714 : zz_in_Pn 1024 714 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 714 (2 * (1024 mod 714))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_715 : zz_in_Pn 1024 715 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 715 (2 * (1024 mod 715))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_716 : zz_in_Pn 1024 716 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 716 (2 * (1024 mod 716))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_717 : zz_in_Pn 1024 717 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 717 (2 * (1024 mod 717))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_718 : zz_in_Pn 1024 718 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 718 (2 * (1024 mod 718))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_719 : zz_in_Pn 1024 719 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 719 (2 * (1024 mod 719))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_720 : zz_in_Pn 1024 720 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 720 (2 * (1024 mod 720))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_721 : zz_in_Pn 1024 721 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 721 (2 * (1024 mod 721))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_722 : zz_in_Pn 1024 722 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 722 (2 * (1024 mod 722))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_723 : zz_in_Pn 1024 723 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 723 (2 * (1024 mod 723))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_724 : zz_in_Pn 1024 724 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 724 (2 * (1024 mod 724))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_725 : zz_in_Pn 1024 725 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 725 (2 * (1024 mod 725))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_726 : zz_in_Pn 1024 726 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 726 (2 * (1024 mod 726))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_727 : zz_in_Pn 1024 727 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 727 (2 * (1024 mod 727))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_728 : zz_in_Pn 1024 728 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 728 (2 * (1024 mod 728))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_729 : zz_in_Pn 1024 729 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 729 (2 * (1024 mod 729))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_730 : zz_in_Pn 1024 730 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 730 (2 * (1024 mod 730))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_731 : zz_in_Pn 1024 731 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 731 (2 * (1024 mod 731))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_732 : zz_in_Pn 1024 732 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 732 (2 * (1024 mod 732))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_733 : zz_in_Pn 1024 733 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 733 (2 * (1024 mod 733))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_734 : zz_in_Pn 1024 734 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 734 (2 * (1024 mod 734))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_735 : zz_in_Pn 1024 735 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 735 (2 * (1024 mod 735))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_736 : zz_in_Pn 1024 736 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 736 (2 * (1024 mod 736))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_737 : zz_in_Pn 1024 737 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 737 (2 * (1024 mod 737))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_738 : zz_in_Pn 1024 738 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 738 (2 * (1024 mod 738))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_739 : zz_in_Pn 1024 739 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 739 (2 * (1024 mod 739))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_740 : zz_in_Pn 1024 740 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 740 (2 * (1024 mod 740))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_741 : zz_in_Pn 1024 741 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 741 (2 * (1024 mod 741))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_742 : zz_in_Pn 1024 742 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 742 (2 * (1024 mod 742))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_743 : zz_in_Pn 1024 743 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 743 (2 * (1024 mod 743))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_744 : zz_in_Pn 1024 744 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 744 (2 * (1024 mod 744))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_745 : zz_in_Pn 1024 745 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 745 (2 * (1024 mod 745))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_746 : zz_in_Pn 1024 746 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 746 (2 * (1024 mod 746))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_747 : zz_in_Pn 1024 747 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 747 (2 * (1024 mod 747))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_748 : zz_in_Pn 1024 748 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 748 (2 * (1024 mod 748))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_749 : zz_in_Pn 1024 749 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 749 (2 * (1024 mod 749))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_750 : zz_in_Pn 1024 750 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 750 (2 * (1024 mod 750))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_751 : zz_in_Pn 1024 751 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 751 (2 * (1024 mod 751))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_752 : zz_in_Pn 1024 752 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 752 (2 * (1024 mod 752))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_753 : zz_in_Pn 1024 753 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 753 (2 * (1024 mod 753))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_754 : zz_in_Pn 1024 754 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 754 (2 * (1024 mod 754))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_755 : zz_in_Pn 1024 755 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 755 (2 * (1024 mod 755))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_756 : zz_in_Pn 1024 756 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 756 (2 * (1024 mod 756))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_757 : zz_in_Pn 1024 757 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 757 (2 * (1024 mod 757))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_758 : zz_in_Pn 1024 758 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 758 (2 * (1024 mod 758))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_759 : zz_in_Pn 1024 759 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 759 (2 * (1024 mod 759))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_760 : zz_in_Pn 1024 760 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 760 (2 * (1024 mod 760))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_761 : zz_in_Pn 1024 761 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 761 (2 * (1024 mod 761))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_762 : zz_in_Pn 1024 762 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 762 (2 * (1024 mod 762))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_763 : zz_in_Pn 1024 763 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 763 (2 * (1024 mod 763))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_764 : zz_in_Pn 1024 764 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 764 (2 * (1024 mod 764))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_765 : zz_in_Pn 1024 765 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 765 (2 * (1024 mod 765))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_766 : zz_in_Pn 1024 766 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 766 (2 * (1024 mod 766))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_767 : zz_in_Pn 1024 767 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 767 (2 * (1024 mod 767))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_768 : zz_in_Pn 1024 768 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 768 (2 * (1024 mod 768))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_769 : zz_in_Pn 1024 769 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 769 (2 * (1024 mod 769))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_770 : zz_in_Pn 1024 770 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 770 (2 * (1024 mod 770))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_771 : zz_in_Pn 1024 771 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 771 (2 * (1024 mod 771))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_772 : zz_in_Pn 1024 772 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 772 (2 * (1024 mod 772))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_773 : zz_in_Pn 1024 773 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 773 (2 * (1024 mod 773))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_774 : zz_in_Pn 1024 774 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 774 (2 * (1024 mod 774))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_775 : zz_in_Pn 1024 775 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 775 (2 * (1024 mod 775))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_776 : zz_in_Pn 1024 776 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 776 (2 * (1024 mod 776))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_777 : zz_in_Pn 1024 777 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 777 (2 * (1024 mod 777))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_778 : zz_in_Pn 1024 778 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 778 (2 * (1024 mod 778))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_779 : zz_in_Pn 1024 779 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 779 (2 * (1024 mod 779))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_780 : zz_in_Pn 1024 780 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 780 (2 * (1024 mod 780))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_781 : zz_in_Pn 1024 781 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 781 (2 * (1024 mod 781))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_782 : zz_in_Pn 1024 782 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 782 (2 * (1024 mod 782))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_783 : zz_in_Pn 1024 783 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 783 (2 * (1024 mod 783))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_784 : zz_in_Pn 1024 784 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 784 (2 * (1024 mod 784))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_785 : zz_in_Pn 1024 785 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 785 (2 * (1024 mod 785))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_786 : zz_in_Pn 1024 786 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 786 (2 * (1024 mod 786))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_787 : zz_in_Pn 1024 787 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 787 (2 * (1024 mod 787))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_788 : zz_in_Pn 1024 788 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 788 (2 * (1024 mod 788))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_789 : zz_in_Pn 1024 789 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 789 (2 * (1024 mod 789))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_790 : zz_in_Pn 1024 790 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 790 (2 * (1024 mod 790))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_791 : zz_in_Pn 1024 791 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 791 (2 * (1024 mod 791))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_792 : zz_in_Pn 1024 792 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 792 (2 * (1024 mod 792))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_793 : zz_in_Pn 1024 793 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 793 (2 * (1024 mod 793))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_794 : zz_in_Pn 1024 794 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 794 (2 * (1024 mod 794))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_795 : zz_in_Pn 1024 795 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 795 (2 * (1024 mod 795))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_796 : zz_in_Pn 1024 796 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 796 (2 * (1024 mod 796))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_797 : zz_in_Pn 1024 797 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 797 (2 * (1024 mod 797))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_798 : zz_in_Pn 1024 798 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 798 (2 * (1024 mod 798))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_799 : zz_in_Pn 1024 799 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 799 (2 * (1024 mod 799))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_800 : zz_in_Pn 1024 800 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 800 (2 * (1024 mod 800))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_801 : zz_in_Pn 1024 801 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 801 (2 * (1024 mod 801))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_802 : zz_in_Pn 1024 802 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 802 (2 * (1024 mod 802))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_803 : zz_in_Pn 1024 803 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 803 (2 * (1024 mod 803))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_804 : zz_in_Pn 1024 804 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 804 (2 * (1024 mod 804))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_805 : zz_in_Pn 1024 805 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 805 (2 * (1024 mod 805))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_806 : zz_in_Pn 1024 806 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 806 (2 * (1024 mod 806))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_807 : zz_in_Pn 1024 807 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 807 (2 * (1024 mod 807))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_808 : zz_in_Pn 1024 808 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 808 (2 * (1024 mod 808))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_809 : zz_in_Pn 1024 809 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 809 (2 * (1024 mod 809))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_810 : zz_in_Pn 1024 810 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 810 (2 * (1024 mod 810))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_811 : zz_in_Pn 1024 811 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 811 (2 * (1024 mod 811))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_812 : zz_in_Pn 1024 812 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 812 (2 * (1024 mod 812))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_813 : zz_in_Pn 1024 813 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 813 (2 * (1024 mod 813))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_814 : zz_in_Pn 1024 814 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 814 (2 * (1024 mod 814))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_815 : zz_in_Pn 1024 815 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 815 (2 * (1024 mod 815))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_816 : zz_in_Pn 1024 816 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 816 (2 * (1024 mod 816))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_817 : zz_in_Pn 1024 817 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 817 (2 * (1024 mod 817))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_818 : zz_in_Pn 1024 818 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 818 (2 * (1024 mod 818))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_819 : zz_in_Pn 1024 819 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 819 (2 * (1024 mod 819))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_820 : zz_in_Pn 1024 820 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 820 (2 * (1024 mod 820))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_821 : zz_in_Pn 1024 821 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 821 (2 * (1024 mod 821))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_822 : zz_in_Pn 1024 822 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 822 (2 * (1024 mod 822))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_823 : zz_in_Pn 1024 823 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 823 (2 * (1024 mod 823))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_824 : zz_in_Pn 1024 824 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 824 (2 * (1024 mod 824))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_825 : zz_in_Pn 1024 825 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 825 (2 * (1024 mod 825))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_826 : zz_in_Pn 1024 826 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 826 (2 * (1024 mod 826))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_827 : zz_in_Pn 1024 827 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 827 (2 * (1024 mod 827))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_828 : zz_in_Pn 1024 828 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 828 (2 * (1024 mod 828))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_829 : zz_in_Pn 1024 829 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 829 (2 * (1024 mod 829))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_830 : zz_in_Pn 1024 830 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 830 (2 * (1024 mod 830))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_831 : zz_in_Pn 1024 831 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 831 (2 * (1024 mod 831))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_832 : zz_in_Pn 1024 832 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 832 (2 * (1024 mod 832))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_833 : zz_in_Pn 1024 833 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 833 (2 * (1024 mod 833))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_834 : zz_in_Pn 1024 834 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 834 (2 * (1024 mod 834))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_835 : zz_in_Pn 1024 835 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 835 (2 * (1024 mod 835))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_836 : zz_in_Pn 1024 836 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 836 (2 * (1024 mod 836))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_837 : zz_in_Pn 1024 837 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 837 (2 * (1024 mod 837))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_838 : zz_in_Pn 1024 838 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 838 (2 * (1024 mod 838))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_839 : zz_in_Pn 1024 839 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 839 (2 * (1024 mod 839))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_840 : zz_in_Pn 1024 840 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 840 (2 * (1024 mod 840))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_841 : zz_in_Pn 1024 841 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 841 (2 * (1024 mod 841))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_842 : zz_in_Pn 1024 842 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 842 (2 * (1024 mod 842))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_843 : zz_in_Pn 1024 843 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 843 (2 * (1024 mod 843))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_844 : zz_in_Pn 1024 844 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 844 (2 * (1024 mod 844))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_845 : zz_in_Pn 1024 845 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 845 (2 * (1024 mod 845))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_846 : zz_in_Pn 1024 846 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 846 (2 * (1024 mod 846))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_847 : zz_in_Pn 1024 847 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 847 (2 * (1024 mod 847))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_848 : zz_in_Pn 1024 848 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 848 (2 * (1024 mod 848))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_849 : zz_in_Pn 1024 849 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 849 (2 * (1024 mod 849))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_850 : zz_in_Pn 1024 850 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 850 (2 * (1024 mod 850))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_851 : zz_in_Pn 1024 851 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 851 (2 * (1024 mod 851))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_852 : zz_in_Pn 1024 852 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 852 (2 * (1024 mod 852))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_853 : zz_in_Pn 1024 853 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 853 (2 * (1024 mod 853))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_854 : zz_in_Pn 1024 854 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 854 (2 * (1024 mod 854))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_855 : zz_in_Pn 1024 855 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 855 (2 * (1024 mod 855))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_856 : zz_in_Pn 1024 856 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 856 (2 * (1024 mod 856))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_857 : zz_in_Pn 1024 857 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 857 (2 * (1024 mod 857))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_858 : zz_in_Pn 1024 858 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 858 (2 * (1024 mod 858))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_859 : zz_in_Pn 1024 859 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 859 (2 * (1024 mod 859))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_860 : zz_in_Pn 1024 860 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 860 (2 * (1024 mod 860))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_861 : zz_in_Pn 1024 861 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 861 (2 * (1024 mod 861))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_862 : zz_in_Pn 1024 862 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 862 (2 * (1024 mod 862))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_863 : zz_in_Pn 1024 863 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 863 (2 * (1024 mod 863))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_864 : zz_in_Pn 1024 864 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 864 (2 * (1024 mod 864))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_865 : zz_in_Pn 1024 865 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 865 (2 * (1024 mod 865))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_866 : zz_in_Pn 1024 866 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 866 (2 * (1024 mod 866))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_867 : zz_in_Pn 1024 867 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 867 (2 * (1024 mod 867))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_868 : zz_in_Pn 1024 868 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 868 (2 * (1024 mod 868))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_869 : zz_in_Pn 1024 869 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 869 (2 * (1024 mod 869))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_870 : zz_in_Pn 1024 870 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 870 (2 * (1024 mod 870))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_871 : zz_in_Pn 1024 871 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 871 (2 * (1024 mod 871))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_872 : zz_in_Pn 1024 872 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 872 (2 * (1024 mod 872))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_873 : zz_in_Pn 1024 873 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 873 (2 * (1024 mod 873))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_874 : zz_in_Pn 1024 874 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 874 (2 * (1024 mod 874))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_875 : zz_in_Pn 1024 875 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 875 (2 * (1024 mod 875))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_876 : zz_in_Pn 1024 876 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 876 (2 * (1024 mod 876))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_877 : zz_in_Pn 1024 877 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 877 (2 * (1024 mod 877))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_878 : zz_in_Pn 1024 878 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 878 (2 * (1024 mod 878))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_879 : zz_in_Pn 1024 879 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 879 (2 * (1024 mod 879))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_880 : zz_in_Pn 1024 880 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 880 (2 * (1024 mod 880))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_881 : zz_in_Pn 1024 881 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 881 (2 * (1024 mod 881))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_882 : zz_in_Pn 1024 882 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 882 (2 * (1024 mod 882))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_883 : zz_in_Pn 1024 883 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 883 (2 * (1024 mod 883))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_884 : zz_in_Pn 1024 884 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 884 (2 * (1024 mod 884))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_885 : zz_in_Pn 1024 885 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 885 (2 * (1024 mod 885))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_886 : zz_in_Pn 1024 886 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 886 (2 * (1024 mod 886))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_887 : zz_in_Pn 1024 887 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 887 (2 * (1024 mod 887))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_888 : zz_in_Pn 1024 888 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 888 (2 * (1024 mod 888))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_889 : zz_in_Pn 1024 889 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 889 (2 * (1024 mod 889))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_890 : zz_in_Pn 1024 890 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 890 (2 * (1024 mod 890))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_891 : zz_in_Pn 1024 891 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 891 (2 * (1024 mod 891))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_892 : zz_in_Pn 1024 892 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 892 (2 * (1024 mod 892))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_893 : zz_in_Pn 1024 893 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 893 (2 * (1024 mod 893))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_894 : zz_in_Pn 1024 894 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 894 (2 * (1024 mod 894))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_895 : zz_in_Pn 1024 895 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 895 (2 * (1024 mod 895))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_896 : zz_in_Pn 1024 896 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 896 (2 * (1024 mod 896))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_897 : zz_in_Pn 1024 897 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 897 (2 * (1024 mod 897))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_898 : zz_in_Pn 1024 898 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 898 (2 * (1024 mod 898))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_899 : zz_in_Pn 1024 899 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 899 (2 * (1024 mod 899))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_900 : zz_in_Pn 1024 900 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 900 (2 * (1024 mod 900))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_901 : zz_in_Pn 1024 901 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 901 (2 * (1024 mod 901))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_902 : zz_in_Pn 1024 902 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 902 (2 * (1024 mod 902))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_903 : zz_in_Pn 1024 903 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 903 (2 * (1024 mod 903))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_904 : zz_in_Pn 1024 904 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 904 (2 * (1024 mod 904))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_905 : zz_in_Pn 1024 905 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 905 (2 * (1024 mod 905))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_906 : zz_in_Pn 1024 906 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 906 (2 * (1024 mod 906))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_907 : zz_in_Pn 1024 907 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 907 (2 * (1024 mod 907))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_908 : zz_in_Pn 1024 908 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 908 (2 * (1024 mod 908))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_909 : zz_in_Pn 1024 909 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 909 (2 * (1024 mod 909))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_910 : zz_in_Pn 1024 910 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 910 (2 * (1024 mod 910))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_911 : zz_in_Pn 1024 911 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 911 (2 * (1024 mod 911))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_912 : zz_in_Pn 1024 912 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 912 (2 * (1024 mod 912))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_913 : zz_in_Pn 1024 913 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 913 (2 * (1024 mod 913))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_914 : zz_in_Pn 1024 914 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 914 (2 * (1024 mod 914))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_915 : zz_in_Pn 1024 915 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 915 (2 * (1024 mod 915))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_916 : zz_in_Pn 1024 916 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 916 (2 * (1024 mod 916))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_917 : zz_in_Pn 1024 917 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 917 (2 * (1024 mod 917))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_918 : zz_in_Pn 1024 918 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 918 (2 * (1024 mod 918))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_919 : zz_in_Pn 1024 919 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 919 (2 * (1024 mod 919))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_920 : zz_in_Pn 1024 920 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 920 (2 * (1024 mod 920))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_921 : zz_in_Pn 1024 921 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 921 (2 * (1024 mod 921))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_922 : zz_in_Pn 1024 922 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 922 (2 * (1024 mod 922))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_923 : zz_in_Pn 1024 923 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 923 (2 * (1024 mod 923))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_924 : zz_in_Pn 1024 924 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 924 (2 * (1024 mod 924))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_925 : zz_in_Pn 1024 925 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 925 (2 * (1024 mod 925))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_926 : zz_in_Pn 1024 926 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 926 (2 * (1024 mod 926))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_927 : zz_in_Pn 1024 927 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 927 (2 * (1024 mod 927))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_928 : zz_in_Pn 1024 928 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 928 (2 * (1024 mod 928))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_929 : zz_in_Pn 1024 929 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 929 (2 * (1024 mod 929))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_930 : zz_in_Pn 1024 930 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 930 (2 * (1024 mod 930))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_931 : zz_in_Pn 1024 931 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 931 (2 * (1024 mod 931))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_932 : zz_in_Pn 1024 932 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 932 (2 * (1024 mod 932))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_933 : zz_in_Pn 1024 933 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 933 (2 * (1024 mod 933))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_934 : zz_in_Pn 1024 934 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 934 (2 * (1024 mod 934))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_935 : zz_in_Pn 1024 935 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 935 (2 * (1024 mod 935))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_936 : zz_in_Pn 1024 936 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 936 (2 * (1024 mod 936))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_937 : zz_in_Pn 1024 937 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 937 (2 * (1024 mod 937))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_938 : zz_in_Pn 1024 938 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 938 (2 * (1024 mod 938))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_939 : zz_in_Pn 1024 939 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 939 (2 * (1024 mod 939))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_940 : zz_in_Pn 1024 940 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 940 (2 * (1024 mod 940))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_941 : zz_in_Pn 1024 941 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 941 (2 * (1024 mod 941))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_942 : zz_in_Pn 1024 942 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 942 (2 * (1024 mod 942))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_943 : zz_in_Pn 1024 943 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 943 (2 * (1024 mod 943))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_944 : zz_in_Pn 1024 944 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 944 (2 * (1024 mod 944))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_945 : zz_in_Pn 1024 945 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 945 (2 * (1024 mod 945))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_946 : zz_in_Pn 1024 946 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 946 (2 * (1024 mod 946))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_947 : zz_in_Pn 1024 947 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 947 (2 * (1024 mod 947))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_948 : zz_in_Pn 1024 948 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 948 (2 * (1024 mod 948))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_949 : zz_in_Pn 1024 949 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 949 (2 * (1024 mod 949))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_950 : zz_in_Pn 1024 950 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 950 (2 * (1024 mod 950))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_951 : zz_in_Pn 1024 951 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 951 (2 * (1024 mod 951))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_952 : zz_in_Pn 1024 952 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 952 (2 * (1024 mod 952))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_953 : zz_in_Pn 1024 953 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 953 (2 * (1024 mod 953))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_954 : zz_in_Pn 1024 954 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 954 (2 * (1024 mod 954))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_955 : zz_in_Pn 1024 955 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 955 (2 * (1024 mod 955))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_956 : zz_in_Pn 1024 956 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 956 (2 * (1024 mod 956))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_957 : zz_in_Pn 1024 957 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 957 (2 * (1024 mod 957))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_958 : zz_in_Pn 1024 958 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 958 (2 * (1024 mod 958))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_959 : zz_in_Pn 1024 959 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 959 (2 * (1024 mod 959))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_960 : zz_in_Pn 1024 960 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 960 (2 * (1024 mod 960))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_961 : zz_in_Pn 1024 961 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 961 (2 * (1024 mod 961))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_962 : zz_in_Pn 1024 962 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 962 (2 * (1024 mod 962))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_963 : zz_in_Pn 1024 963 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 963 (2 * (1024 mod 963))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_964 : zz_in_Pn 1024 964 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 964 (2 * (1024 mod 964))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_965 : zz_in_Pn 1024 965 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 965 (2 * (1024 mod 965))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_966 : zz_in_Pn 1024 966 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 966 (2 * (1024 mod 966))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_967 : zz_in_Pn 1024 967 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 967 (2 * (1024 mod 967))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_968 : zz_in_Pn 1024 968 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 968 (2 * (1024 mod 968))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_969 : zz_in_Pn 1024 969 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 969 (2 * (1024 mod 969))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_970 : zz_in_Pn 1024 970 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 970 (2 * (1024 mod 970))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_971 : zz_in_Pn 1024 971 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 971 (2 * (1024 mod 971))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_972 : zz_in_Pn 1024 972 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 972 (2 * (1024 mod 972))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_973 : zz_in_Pn 1024 973 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 973 (2 * (1024 mod 973))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_974 : zz_in_Pn 1024 974 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 974 (2 * (1024 mod 974))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_975 : zz_in_Pn 1024 975 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 975 (2 * (1024 mod 975))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_976 : zz_in_Pn 1024 976 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 976 (2 * (1024 mod 976))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_977 : zz_in_Pn 1024 977 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 977 (2 * (1024 mod 977))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_978 : zz_in_Pn 1024 978 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 978 (2 * (1024 mod 978))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_979 : zz_in_Pn 1024 979 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 979 (2 * (1024 mod 979))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_980 : zz_in_Pn 1024 980 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 980 (2 * (1024 mod 980))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_981 : zz_in_Pn 1024 981 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 981 (2 * (1024 mod 981))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_982 : zz_in_Pn 1024 982 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 982 (2 * (1024 mod 982))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_983 : zz_in_Pn 1024 983 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 983 (2 * (1024 mod 983))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_984 : zz_in_Pn 1024 984 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 984 (2 * (1024 mod 984))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_985 : zz_in_Pn 1024 985 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 985 (2 * (1024 mod 985))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_986 : zz_in_Pn 1024 986 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 986 (2 * (1024 mod 986))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_987 : zz_in_Pn 1024 987 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 987 (2 * (1024 mod 987))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_988 : zz_in_Pn 1024 988 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 988 (2 * (1024 mod 988))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_989 : zz_in_Pn 1024 989 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 989 (2 * (1024 mod 989))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_990 : zz_in_Pn 1024 990 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 990 (2 * (1024 mod 990))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_991 : zz_in_Pn 1024 991 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 991 (2 * (1024 mod 991))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_992 : zz_in_Pn 1024 992 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 992 (2 * (1024 mod 992))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_993 : zz_in_Pn 1024 993 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 993 (2 * (1024 mod 993))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_994 : zz_in_Pn 1024 994 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 994 (2 * (1024 mod 994))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_995 : zz_in_Pn 1024 995 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 995 (2 * (1024 mod 995))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_996 : zz_in_Pn 1024 996 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 996 (2 * (1024 mod 996))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_997 : zz_in_Pn 1024 997 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 997 (2 * (1024 mod 997))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_998 : zz_in_Pn 1024 998 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 998 (2 * (1024 mod 998))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_999 : zz_in_Pn 1024 999 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 999 (2 * (1024 mod 999))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1000 : zz_in_Pn 1024 1000 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1000 (2 * (1024 mod 1000))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1001 : zz_in_Pn 1024 1001 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1001 (2 * (1024 mod 1001))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1002 : zz_in_Pn 1024 1002 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1002 (2 * (1024 mod 1002))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1003 : zz_in_Pn 1024 1003 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1003 (2 * (1024 mod 1003))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1004 : zz_in_Pn 1024 1004 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1004 (2 * (1024 mod 1004))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1005 : zz_in_Pn 1024 1005 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1005 (2 * (1024 mod 1005))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1006 : zz_in_Pn 1024 1006 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1006 (2 * (1024 mod 1006))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1007 : zz_in_Pn 1024 1007 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1007 (2 * (1024 mod 1007))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1008 : zz_in_Pn 1024 1008 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1008 (2 * (1024 mod 1008))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1009 : zz_in_Pn 1024 1009 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1009 (2 * (1024 mod 1009))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1010 : zz_in_Pn 1024 1010 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1010 (2 * (1024 mod 1010))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1011 : zz_in_Pn 1024 1011 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1011 (2 * (1024 mod 1011))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1012 : zz_in_Pn 1024 1012 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1012 (2 * (1024 mod 1012))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1013 : zz_in_Pn 1024 1013 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1013 (2 * (1024 mod 1013))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1014 : zz_in_Pn 1024 1014 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1014 (2 * (1024 mod 1014))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1015 : zz_in_Pn 1024 1015 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1015 (2 * (1024 mod 1015))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1016 : zz_in_Pn 1024 1016 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1016 (2 * (1024 mod 1016))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1017 : zz_in_Pn 1024 1017 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1017 (2 * (1024 mod 1017))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1018 : zz_in_Pn 1024 1018 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1018 (2 * (1024 mod 1018))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1019 : zz_in_Pn 1024 1019 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1019 (2 * (1024 mod 1019))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1020 : zz_in_Pn 1024 1020 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1020 (2 * (1024 mod 1020))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1021 : zz_in_Pn 1024 1021 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1021 (2 * (1024 mod 1021))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1022 : zz_in_Pn 1024 1022 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1022 (2 * (1024 mod 1022))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1023 : zz_in_Pn 1024 1023 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1023 (2 * (1024 mod 1023))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1024 : zz_in_Pn 1024 1024 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.leb 1024 (2 * (1024 mod 1024))) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

