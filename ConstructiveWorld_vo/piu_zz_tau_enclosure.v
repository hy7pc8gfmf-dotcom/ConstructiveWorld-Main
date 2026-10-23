(* piu_zz_tau_enclosure.v — 消费面：zz_Phi / zz_L / qpow 字面值链、
   带样点（piu_zz_band_*）与审计段（Print Assumptions + Extraction）。
   使命：消费四段 zz_in_Pn 逐点表与 base 段字面值，闭合 τ 面数值链。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖
   bank1..bank3 与 base）、piu_zz_poincare_engine、piu_zz_padic_clearing、
   Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   构造性：本片语句零假设、零公理；三主定理出节全称化形位于 base 段。
   编译配方: coqc -native-compiler no -q -Q . "" piu_zz_tau_enclosure.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* zz_Phi 256 字面值链。 *)
Definition piu_zz_lit_Phi_256 : Z := 10531954717205949017997279253314421329492748083002717783603484345653957%Z.
Lemma piu_zz_zzPhi_256 : zz_Phi 256 = piu_zz_lit_Phi_256.
Proof.
  unfold zz_Phi.
  replace (2 * 256)%nat with 512%nat by lia.
  vm_compute. reflexivity.
Qed.

(* zz_Phi 512 字面值链。 *)
Definition piu_zz_lit_Phibase_512 : Z := 10450272394096255644816989%Z.
Lemma piu_zz_Phibase_512 : zz_prodf 512 512 = piu_zz_lit_Phibase_512.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_Phi_512 : Z := 173295236299308448593556905083609058155631866250228657065711436893134800997337914581124422241893724245071046206461595926053757363611401%Z.
Lemma piu_zz_zzPhi_512 : zz_Phi 512 = piu_zz_lit_Phi_512.
Proof.
  unfold zz_Phi.
  replace (2 * 512)%nat with (512 + 512)%nat by lia.
  rewrite (piu_zz_zprod_merge 512%nat 512%nat 512%nat).
  rewrite piu_zz_Phibase_512.
  assert (Hs : forall x a b : nat, piu_zz_zprod_seg 512%nat x (a + b)%nat = piu_zz_zprod_seg 512%nat x a * piu_zz_zprod_seg 512%nat (x + a)%nat b).
  { intros x a b. induction b as [|c IH].
    - cbn [piu_zz_zprod_seg]. rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
    - replace (a + S c)%nat with (S (a + c))%nat by lia.
      cbn [piu_zz_zprod_seg].
      replace (S (x + a + c))%nat with (S (x + (a + c)))%nat by lia.
      rewrite IH. rewrite Z.mul_assoc. reflexivity. }
  change (piu_zz_zprod_seg 512%nat 512%nat 512%nat) with (piu_zz_zprod_seg 512%nat 512%nat (496%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 496%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 496%nat) with (piu_zz_zprod_seg 512%nat 512%nat (480%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 480%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 480%nat) with (piu_zz_zprod_seg 512%nat 512%nat (464%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 464%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 464%nat) with (piu_zz_zprod_seg 512%nat 512%nat (448%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 448%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 448%nat) with (piu_zz_zprod_seg 512%nat 512%nat (432%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 432%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 432%nat) with (piu_zz_zprod_seg 512%nat 512%nat (416%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 416%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 416%nat) with (piu_zz_zprod_seg 512%nat 512%nat (400%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 400%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 400%nat) with (piu_zz_zprod_seg 512%nat 512%nat (384%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 384%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 384%nat) with (piu_zz_zprod_seg 512%nat 512%nat (368%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 368%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 368%nat) with (piu_zz_zprod_seg 512%nat 512%nat (352%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 352%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 352%nat) with (piu_zz_zprod_seg 512%nat 512%nat (336%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 336%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 336%nat) with (piu_zz_zprod_seg 512%nat 512%nat (320%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 320%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 320%nat) with (piu_zz_zprod_seg 512%nat 512%nat (304%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 304%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 304%nat) with (piu_zz_zprod_seg 512%nat 512%nat (288%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 288%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 288%nat) with (piu_zz_zprod_seg 512%nat 512%nat (272%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 272%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 272%nat) with (piu_zz_zprod_seg 512%nat 512%nat (256%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 256%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 256%nat) with (piu_zz_zprod_seg 512%nat 512%nat (240%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 240%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 240%nat) with (piu_zz_zprod_seg 512%nat 512%nat (224%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 224%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 224%nat) with (piu_zz_zprod_seg 512%nat 512%nat (208%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 208%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 208%nat) with (piu_zz_zprod_seg 512%nat 512%nat (192%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 192%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 192%nat) with (piu_zz_zprod_seg 512%nat 512%nat (176%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 176%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 176%nat) with (piu_zz_zprod_seg 512%nat 512%nat (160%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 160%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 160%nat) with (piu_zz_zprod_seg 512%nat 512%nat (144%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 144%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 144%nat) with (piu_zz_zprod_seg 512%nat 512%nat (128%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 128%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 128%nat) with (piu_zz_zprod_seg 512%nat 512%nat (112%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 112%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 112%nat) with (piu_zz_zprod_seg 512%nat 512%nat (96%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 96%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 96%nat) with (piu_zz_zprod_seg 512%nat 512%nat (80%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 80%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 80%nat) with (piu_zz_zprod_seg 512%nat 512%nat (64%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 64%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 64%nat) with (piu_zz_zprod_seg 512%nat 512%nat (48%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 48%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 48%nat) with (piu_zz_zprod_seg 512%nat 512%nat (32%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 32%nat 16%nat).
  change (piu_zz_zprod_seg 512%nat 512%nat 32%nat) with (piu_zz_zprod_seg 512%nat 512%nat (16%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 16%nat 16%nat).
  assert (Hb0 : piu_zz_zprod_seg 512%nat (512%nat + 496%nat) 16%nat = ((if zz_in_Pn 512 1009%nat then Z.of_nat 1009%nat else 1%Z) * ((if zz_in_Pn 512 1010%nat then Z.of_nat 1010%nat else 1%Z) * ((if zz_in_Pn 512 1011%nat then Z.of_nat 1011%nat else 1%Z) * ((if zz_in_Pn 512 1012%nat then Z.of_nat 1012%nat else 1%Z) * ((if zz_in_Pn 512 1013%nat then Z.of_nat 1013%nat else 1%Z) * ((if zz_in_Pn 512 1014%nat then Z.of_nat 1014%nat else 1%Z) * ((if zz_in_Pn 512 1015%nat then Z.of_nat 1015%nat else 1%Z) * ((if zz_in_Pn 512 1016%nat then Z.of_nat 1016%nat else 1%Z) * ((if zz_in_Pn 512 1017%nat then Z.of_nat 1017%nat else 1%Z) * ((if zz_in_Pn 512 1018%nat then Z.of_nat 1018%nat else 1%Z) * ((if zz_in_Pn 512 1019%nat then Z.of_nat 1019%nat else 1%Z) * ((if zz_in_Pn 512 1020%nat then Z.of_nat 1020%nat else 1%Z) * ((if zz_in_Pn 512 1021%nat then Z.of_nat 1021%nat else 1%Z) * ((if zz_in_Pn 512 1022%nat then Z.of_nat 1022%nat else 1%Z) * ((if zz_in_Pn 512 1023%nat then Z.of_nat 1023%nat else 1%Z) * (if zz_in_Pn 512 1024%nat then Z.of_nat 1024%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_1024.
    rewrite piu_zz_inPn_512_1023.
    rewrite piu_zz_inPn_512_1022.
    rewrite piu_zz_inPn_512_1021.
    rewrite piu_zz_inPn_512_1020.
    rewrite piu_zz_inPn_512_1019.
    rewrite piu_zz_inPn_512_1018.
    rewrite piu_zz_inPn_512_1017.
    rewrite piu_zz_inPn_512_1016.
    rewrite piu_zz_inPn_512_1015.
    rewrite piu_zz_inPn_512_1014.
    rewrite piu_zz_inPn_512_1013.
    rewrite piu_zz_inPn_512_1012.
    rewrite piu_zz_inPn_512_1011.
    rewrite piu_zz_inPn_512_1010.
    rewrite piu_zz_inPn_512_1009.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb1 : piu_zz_zprod_seg 512%nat (512%nat + 480%nat) 16%nat = ((if zz_in_Pn 512 993%nat then Z.of_nat 993%nat else 1%Z) * ((if zz_in_Pn 512 994%nat then Z.of_nat 994%nat else 1%Z) * ((if zz_in_Pn 512 995%nat then Z.of_nat 995%nat else 1%Z) * ((if zz_in_Pn 512 996%nat then Z.of_nat 996%nat else 1%Z) * ((if zz_in_Pn 512 997%nat then Z.of_nat 997%nat else 1%Z) * ((if zz_in_Pn 512 998%nat then Z.of_nat 998%nat else 1%Z) * ((if zz_in_Pn 512 999%nat then Z.of_nat 999%nat else 1%Z) * ((if zz_in_Pn 512 1000%nat then Z.of_nat 1000%nat else 1%Z) * ((if zz_in_Pn 512 1001%nat then Z.of_nat 1001%nat else 1%Z) * ((if zz_in_Pn 512 1002%nat then Z.of_nat 1002%nat else 1%Z) * ((if zz_in_Pn 512 1003%nat then Z.of_nat 1003%nat else 1%Z) * ((if zz_in_Pn 512 1004%nat then Z.of_nat 1004%nat else 1%Z) * ((if zz_in_Pn 512 1005%nat then Z.of_nat 1005%nat else 1%Z) * ((if zz_in_Pn 512 1006%nat then Z.of_nat 1006%nat else 1%Z) * ((if zz_in_Pn 512 1007%nat then Z.of_nat 1007%nat else 1%Z) * (if zz_in_Pn 512 1008%nat then Z.of_nat 1008%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_1008.
    rewrite piu_zz_inPn_512_1007.
    rewrite piu_zz_inPn_512_1006.
    rewrite piu_zz_inPn_512_1005.
    rewrite piu_zz_inPn_512_1004.
    rewrite piu_zz_inPn_512_1003.
    rewrite piu_zz_inPn_512_1002.
    rewrite piu_zz_inPn_512_1001.
    rewrite piu_zz_inPn_512_1000.
    rewrite piu_zz_inPn_512_999.
    rewrite piu_zz_inPn_512_998.
    rewrite piu_zz_inPn_512_997.
    rewrite piu_zz_inPn_512_996.
    rewrite piu_zz_inPn_512_995.
    rewrite piu_zz_inPn_512_994.
    rewrite piu_zz_inPn_512_993.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb2 : piu_zz_zprod_seg 512%nat (512%nat + 464%nat) 16%nat = ((if zz_in_Pn 512 977%nat then Z.of_nat 977%nat else 1%Z) * ((if zz_in_Pn 512 978%nat then Z.of_nat 978%nat else 1%Z) * ((if zz_in_Pn 512 979%nat then Z.of_nat 979%nat else 1%Z) * ((if zz_in_Pn 512 980%nat then Z.of_nat 980%nat else 1%Z) * ((if zz_in_Pn 512 981%nat then Z.of_nat 981%nat else 1%Z) * ((if zz_in_Pn 512 982%nat then Z.of_nat 982%nat else 1%Z) * ((if zz_in_Pn 512 983%nat then Z.of_nat 983%nat else 1%Z) * ((if zz_in_Pn 512 984%nat then Z.of_nat 984%nat else 1%Z) * ((if zz_in_Pn 512 985%nat then Z.of_nat 985%nat else 1%Z) * ((if zz_in_Pn 512 986%nat then Z.of_nat 986%nat else 1%Z) * ((if zz_in_Pn 512 987%nat then Z.of_nat 987%nat else 1%Z) * ((if zz_in_Pn 512 988%nat then Z.of_nat 988%nat else 1%Z) * ((if zz_in_Pn 512 989%nat then Z.of_nat 989%nat else 1%Z) * ((if zz_in_Pn 512 990%nat then Z.of_nat 990%nat else 1%Z) * ((if zz_in_Pn 512 991%nat then Z.of_nat 991%nat else 1%Z) * (if zz_in_Pn 512 992%nat then Z.of_nat 992%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_992.
    rewrite piu_zz_inPn_512_991.
    rewrite piu_zz_inPn_512_990.
    rewrite piu_zz_inPn_512_989.
    rewrite piu_zz_inPn_512_988.
    rewrite piu_zz_inPn_512_987.
    rewrite piu_zz_inPn_512_986.
    rewrite piu_zz_inPn_512_985.
    rewrite piu_zz_inPn_512_984.
    rewrite piu_zz_inPn_512_983.
    rewrite piu_zz_inPn_512_982.
    rewrite piu_zz_inPn_512_981.
    rewrite piu_zz_inPn_512_980.
    rewrite piu_zz_inPn_512_979.
    rewrite piu_zz_inPn_512_978.
    rewrite piu_zz_inPn_512_977.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb3 : piu_zz_zprod_seg 512%nat (512%nat + 448%nat) 16%nat = ((if zz_in_Pn 512 961%nat then Z.of_nat 961%nat else 1%Z) * ((if zz_in_Pn 512 962%nat then Z.of_nat 962%nat else 1%Z) * ((if zz_in_Pn 512 963%nat then Z.of_nat 963%nat else 1%Z) * ((if zz_in_Pn 512 964%nat then Z.of_nat 964%nat else 1%Z) * ((if zz_in_Pn 512 965%nat then Z.of_nat 965%nat else 1%Z) * ((if zz_in_Pn 512 966%nat then Z.of_nat 966%nat else 1%Z) * ((if zz_in_Pn 512 967%nat then Z.of_nat 967%nat else 1%Z) * ((if zz_in_Pn 512 968%nat then Z.of_nat 968%nat else 1%Z) * ((if zz_in_Pn 512 969%nat then Z.of_nat 969%nat else 1%Z) * ((if zz_in_Pn 512 970%nat then Z.of_nat 970%nat else 1%Z) * ((if zz_in_Pn 512 971%nat then Z.of_nat 971%nat else 1%Z) * ((if zz_in_Pn 512 972%nat then Z.of_nat 972%nat else 1%Z) * ((if zz_in_Pn 512 973%nat then Z.of_nat 973%nat else 1%Z) * ((if zz_in_Pn 512 974%nat then Z.of_nat 974%nat else 1%Z) * ((if zz_in_Pn 512 975%nat then Z.of_nat 975%nat else 1%Z) * (if zz_in_Pn 512 976%nat then Z.of_nat 976%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_976.
    rewrite piu_zz_inPn_512_975.
    rewrite piu_zz_inPn_512_974.
    rewrite piu_zz_inPn_512_973.
    rewrite piu_zz_inPn_512_972.
    rewrite piu_zz_inPn_512_971.
    rewrite piu_zz_inPn_512_970.
    rewrite piu_zz_inPn_512_969.
    rewrite piu_zz_inPn_512_968.
    rewrite piu_zz_inPn_512_967.
    rewrite piu_zz_inPn_512_966.
    rewrite piu_zz_inPn_512_965.
    rewrite piu_zz_inPn_512_964.
    rewrite piu_zz_inPn_512_963.
    rewrite piu_zz_inPn_512_962.
    rewrite piu_zz_inPn_512_961.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb4 : piu_zz_zprod_seg 512%nat (512%nat + 432%nat) 16%nat = ((if zz_in_Pn 512 945%nat then Z.of_nat 945%nat else 1%Z) * ((if zz_in_Pn 512 946%nat then Z.of_nat 946%nat else 1%Z) * ((if zz_in_Pn 512 947%nat then Z.of_nat 947%nat else 1%Z) * ((if zz_in_Pn 512 948%nat then Z.of_nat 948%nat else 1%Z) * ((if zz_in_Pn 512 949%nat then Z.of_nat 949%nat else 1%Z) * ((if zz_in_Pn 512 950%nat then Z.of_nat 950%nat else 1%Z) * ((if zz_in_Pn 512 951%nat then Z.of_nat 951%nat else 1%Z) * ((if zz_in_Pn 512 952%nat then Z.of_nat 952%nat else 1%Z) * ((if zz_in_Pn 512 953%nat then Z.of_nat 953%nat else 1%Z) * ((if zz_in_Pn 512 954%nat then Z.of_nat 954%nat else 1%Z) * ((if zz_in_Pn 512 955%nat then Z.of_nat 955%nat else 1%Z) * ((if zz_in_Pn 512 956%nat then Z.of_nat 956%nat else 1%Z) * ((if zz_in_Pn 512 957%nat then Z.of_nat 957%nat else 1%Z) * ((if zz_in_Pn 512 958%nat then Z.of_nat 958%nat else 1%Z) * ((if zz_in_Pn 512 959%nat then Z.of_nat 959%nat else 1%Z) * (if zz_in_Pn 512 960%nat then Z.of_nat 960%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_960.
    rewrite piu_zz_inPn_512_959.
    rewrite piu_zz_inPn_512_958.
    rewrite piu_zz_inPn_512_957.
    rewrite piu_zz_inPn_512_956.
    rewrite piu_zz_inPn_512_955.
    rewrite piu_zz_inPn_512_954.
    rewrite piu_zz_inPn_512_953.
    rewrite piu_zz_inPn_512_952.
    rewrite piu_zz_inPn_512_951.
    rewrite piu_zz_inPn_512_950.
    rewrite piu_zz_inPn_512_949.
    rewrite piu_zz_inPn_512_948.
    rewrite piu_zz_inPn_512_947.
    rewrite piu_zz_inPn_512_946.
    rewrite piu_zz_inPn_512_945.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb5 : piu_zz_zprod_seg 512%nat (512%nat + 416%nat) 16%nat = ((if zz_in_Pn 512 929%nat then Z.of_nat 929%nat else 1%Z) * ((if zz_in_Pn 512 930%nat then Z.of_nat 930%nat else 1%Z) * ((if zz_in_Pn 512 931%nat then Z.of_nat 931%nat else 1%Z) * ((if zz_in_Pn 512 932%nat then Z.of_nat 932%nat else 1%Z) * ((if zz_in_Pn 512 933%nat then Z.of_nat 933%nat else 1%Z) * ((if zz_in_Pn 512 934%nat then Z.of_nat 934%nat else 1%Z) * ((if zz_in_Pn 512 935%nat then Z.of_nat 935%nat else 1%Z) * ((if zz_in_Pn 512 936%nat then Z.of_nat 936%nat else 1%Z) * ((if zz_in_Pn 512 937%nat then Z.of_nat 937%nat else 1%Z) * ((if zz_in_Pn 512 938%nat then Z.of_nat 938%nat else 1%Z) * ((if zz_in_Pn 512 939%nat then Z.of_nat 939%nat else 1%Z) * ((if zz_in_Pn 512 940%nat then Z.of_nat 940%nat else 1%Z) * ((if zz_in_Pn 512 941%nat then Z.of_nat 941%nat else 1%Z) * ((if zz_in_Pn 512 942%nat then Z.of_nat 942%nat else 1%Z) * ((if zz_in_Pn 512 943%nat then Z.of_nat 943%nat else 1%Z) * (if zz_in_Pn 512 944%nat then Z.of_nat 944%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_944.
    rewrite piu_zz_inPn_512_943.
    rewrite piu_zz_inPn_512_942.
    rewrite piu_zz_inPn_512_941.
    rewrite piu_zz_inPn_512_940.
    rewrite piu_zz_inPn_512_939.
    rewrite piu_zz_inPn_512_938.
    rewrite piu_zz_inPn_512_937.
    rewrite piu_zz_inPn_512_936.
    rewrite piu_zz_inPn_512_935.
    rewrite piu_zz_inPn_512_934.
    rewrite piu_zz_inPn_512_933.
    rewrite piu_zz_inPn_512_932.
    rewrite piu_zz_inPn_512_931.
    rewrite piu_zz_inPn_512_930.
    rewrite piu_zz_inPn_512_929.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb6 : piu_zz_zprod_seg 512%nat (512%nat + 400%nat) 16%nat = ((if zz_in_Pn 512 913%nat then Z.of_nat 913%nat else 1%Z) * ((if zz_in_Pn 512 914%nat then Z.of_nat 914%nat else 1%Z) * ((if zz_in_Pn 512 915%nat then Z.of_nat 915%nat else 1%Z) * ((if zz_in_Pn 512 916%nat then Z.of_nat 916%nat else 1%Z) * ((if zz_in_Pn 512 917%nat then Z.of_nat 917%nat else 1%Z) * ((if zz_in_Pn 512 918%nat then Z.of_nat 918%nat else 1%Z) * ((if zz_in_Pn 512 919%nat then Z.of_nat 919%nat else 1%Z) * ((if zz_in_Pn 512 920%nat then Z.of_nat 920%nat else 1%Z) * ((if zz_in_Pn 512 921%nat then Z.of_nat 921%nat else 1%Z) * ((if zz_in_Pn 512 922%nat then Z.of_nat 922%nat else 1%Z) * ((if zz_in_Pn 512 923%nat then Z.of_nat 923%nat else 1%Z) * ((if zz_in_Pn 512 924%nat then Z.of_nat 924%nat else 1%Z) * ((if zz_in_Pn 512 925%nat then Z.of_nat 925%nat else 1%Z) * ((if zz_in_Pn 512 926%nat then Z.of_nat 926%nat else 1%Z) * ((if zz_in_Pn 512 927%nat then Z.of_nat 927%nat else 1%Z) * (if zz_in_Pn 512 928%nat then Z.of_nat 928%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_928.
    rewrite piu_zz_inPn_512_927.
    rewrite piu_zz_inPn_512_926.
    rewrite piu_zz_inPn_512_925.
    rewrite piu_zz_inPn_512_924.
    rewrite piu_zz_inPn_512_923.
    rewrite piu_zz_inPn_512_922.
    rewrite piu_zz_inPn_512_921.
    rewrite piu_zz_inPn_512_920.
    rewrite piu_zz_inPn_512_919.
    rewrite piu_zz_inPn_512_918.
    rewrite piu_zz_inPn_512_917.
    rewrite piu_zz_inPn_512_916.
    rewrite piu_zz_inPn_512_915.
    rewrite piu_zz_inPn_512_914.
    rewrite piu_zz_inPn_512_913.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb7 : piu_zz_zprod_seg 512%nat (512%nat + 384%nat) 16%nat = ((if zz_in_Pn 512 897%nat then Z.of_nat 897%nat else 1%Z) * ((if zz_in_Pn 512 898%nat then Z.of_nat 898%nat else 1%Z) * ((if zz_in_Pn 512 899%nat then Z.of_nat 899%nat else 1%Z) * ((if zz_in_Pn 512 900%nat then Z.of_nat 900%nat else 1%Z) * ((if zz_in_Pn 512 901%nat then Z.of_nat 901%nat else 1%Z) * ((if zz_in_Pn 512 902%nat then Z.of_nat 902%nat else 1%Z) * ((if zz_in_Pn 512 903%nat then Z.of_nat 903%nat else 1%Z) * ((if zz_in_Pn 512 904%nat then Z.of_nat 904%nat else 1%Z) * ((if zz_in_Pn 512 905%nat then Z.of_nat 905%nat else 1%Z) * ((if zz_in_Pn 512 906%nat then Z.of_nat 906%nat else 1%Z) * ((if zz_in_Pn 512 907%nat then Z.of_nat 907%nat else 1%Z) * ((if zz_in_Pn 512 908%nat then Z.of_nat 908%nat else 1%Z) * ((if zz_in_Pn 512 909%nat then Z.of_nat 909%nat else 1%Z) * ((if zz_in_Pn 512 910%nat then Z.of_nat 910%nat else 1%Z) * ((if zz_in_Pn 512 911%nat then Z.of_nat 911%nat else 1%Z) * (if zz_in_Pn 512 912%nat then Z.of_nat 912%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_912.
    rewrite piu_zz_inPn_512_911.
    rewrite piu_zz_inPn_512_910.
    rewrite piu_zz_inPn_512_909.
    rewrite piu_zz_inPn_512_908.
    rewrite piu_zz_inPn_512_907.
    rewrite piu_zz_inPn_512_906.
    rewrite piu_zz_inPn_512_905.
    rewrite piu_zz_inPn_512_904.
    rewrite piu_zz_inPn_512_903.
    rewrite piu_zz_inPn_512_902.
    rewrite piu_zz_inPn_512_901.
    rewrite piu_zz_inPn_512_900.
    rewrite piu_zz_inPn_512_899.
    rewrite piu_zz_inPn_512_898.
    rewrite piu_zz_inPn_512_897.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb8 : piu_zz_zprod_seg 512%nat (512%nat + 368%nat) 16%nat = ((if zz_in_Pn 512 881%nat then Z.of_nat 881%nat else 1%Z) * ((if zz_in_Pn 512 882%nat then Z.of_nat 882%nat else 1%Z) * ((if zz_in_Pn 512 883%nat then Z.of_nat 883%nat else 1%Z) * ((if zz_in_Pn 512 884%nat then Z.of_nat 884%nat else 1%Z) * ((if zz_in_Pn 512 885%nat then Z.of_nat 885%nat else 1%Z) * ((if zz_in_Pn 512 886%nat then Z.of_nat 886%nat else 1%Z) * ((if zz_in_Pn 512 887%nat then Z.of_nat 887%nat else 1%Z) * ((if zz_in_Pn 512 888%nat then Z.of_nat 888%nat else 1%Z) * ((if zz_in_Pn 512 889%nat then Z.of_nat 889%nat else 1%Z) * ((if zz_in_Pn 512 890%nat then Z.of_nat 890%nat else 1%Z) * ((if zz_in_Pn 512 891%nat then Z.of_nat 891%nat else 1%Z) * ((if zz_in_Pn 512 892%nat then Z.of_nat 892%nat else 1%Z) * ((if zz_in_Pn 512 893%nat then Z.of_nat 893%nat else 1%Z) * ((if zz_in_Pn 512 894%nat then Z.of_nat 894%nat else 1%Z) * ((if zz_in_Pn 512 895%nat then Z.of_nat 895%nat else 1%Z) * (if zz_in_Pn 512 896%nat then Z.of_nat 896%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_896.
    rewrite piu_zz_inPn_512_895.
    rewrite piu_zz_inPn_512_894.
    rewrite piu_zz_inPn_512_893.
    rewrite piu_zz_inPn_512_892.
    rewrite piu_zz_inPn_512_891.
    rewrite piu_zz_inPn_512_890.
    rewrite piu_zz_inPn_512_889.
    rewrite piu_zz_inPn_512_888.
    rewrite piu_zz_inPn_512_887.
    rewrite piu_zz_inPn_512_886.
    rewrite piu_zz_inPn_512_885.
    rewrite piu_zz_inPn_512_884.
    rewrite piu_zz_inPn_512_883.
    rewrite piu_zz_inPn_512_882.
    rewrite piu_zz_inPn_512_881.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb9 : piu_zz_zprod_seg 512%nat (512%nat + 352%nat) 16%nat = ((if zz_in_Pn 512 865%nat then Z.of_nat 865%nat else 1%Z) * ((if zz_in_Pn 512 866%nat then Z.of_nat 866%nat else 1%Z) * ((if zz_in_Pn 512 867%nat then Z.of_nat 867%nat else 1%Z) * ((if zz_in_Pn 512 868%nat then Z.of_nat 868%nat else 1%Z) * ((if zz_in_Pn 512 869%nat then Z.of_nat 869%nat else 1%Z) * ((if zz_in_Pn 512 870%nat then Z.of_nat 870%nat else 1%Z) * ((if zz_in_Pn 512 871%nat then Z.of_nat 871%nat else 1%Z) * ((if zz_in_Pn 512 872%nat then Z.of_nat 872%nat else 1%Z) * ((if zz_in_Pn 512 873%nat then Z.of_nat 873%nat else 1%Z) * ((if zz_in_Pn 512 874%nat then Z.of_nat 874%nat else 1%Z) * ((if zz_in_Pn 512 875%nat then Z.of_nat 875%nat else 1%Z) * ((if zz_in_Pn 512 876%nat then Z.of_nat 876%nat else 1%Z) * ((if zz_in_Pn 512 877%nat then Z.of_nat 877%nat else 1%Z) * ((if zz_in_Pn 512 878%nat then Z.of_nat 878%nat else 1%Z) * ((if zz_in_Pn 512 879%nat then Z.of_nat 879%nat else 1%Z) * (if zz_in_Pn 512 880%nat then Z.of_nat 880%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_880.
    rewrite piu_zz_inPn_512_879.
    rewrite piu_zz_inPn_512_878.
    rewrite piu_zz_inPn_512_877.
    rewrite piu_zz_inPn_512_876.
    rewrite piu_zz_inPn_512_875.
    rewrite piu_zz_inPn_512_874.
    rewrite piu_zz_inPn_512_873.
    rewrite piu_zz_inPn_512_872.
    rewrite piu_zz_inPn_512_871.
    rewrite piu_zz_inPn_512_870.
    rewrite piu_zz_inPn_512_869.
    rewrite piu_zz_inPn_512_868.
    rewrite piu_zz_inPn_512_867.
    rewrite piu_zz_inPn_512_866.
    rewrite piu_zz_inPn_512_865.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb10 : piu_zz_zprod_seg 512%nat (512%nat + 336%nat) 16%nat = ((if zz_in_Pn 512 849%nat then Z.of_nat 849%nat else 1%Z) * ((if zz_in_Pn 512 850%nat then Z.of_nat 850%nat else 1%Z) * ((if zz_in_Pn 512 851%nat then Z.of_nat 851%nat else 1%Z) * ((if zz_in_Pn 512 852%nat then Z.of_nat 852%nat else 1%Z) * ((if zz_in_Pn 512 853%nat then Z.of_nat 853%nat else 1%Z) * ((if zz_in_Pn 512 854%nat then Z.of_nat 854%nat else 1%Z) * ((if zz_in_Pn 512 855%nat then Z.of_nat 855%nat else 1%Z) * ((if zz_in_Pn 512 856%nat then Z.of_nat 856%nat else 1%Z) * ((if zz_in_Pn 512 857%nat then Z.of_nat 857%nat else 1%Z) * ((if zz_in_Pn 512 858%nat then Z.of_nat 858%nat else 1%Z) * ((if zz_in_Pn 512 859%nat then Z.of_nat 859%nat else 1%Z) * ((if zz_in_Pn 512 860%nat then Z.of_nat 860%nat else 1%Z) * ((if zz_in_Pn 512 861%nat then Z.of_nat 861%nat else 1%Z) * ((if zz_in_Pn 512 862%nat then Z.of_nat 862%nat else 1%Z) * ((if zz_in_Pn 512 863%nat then Z.of_nat 863%nat else 1%Z) * (if zz_in_Pn 512 864%nat then Z.of_nat 864%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_864.
    rewrite piu_zz_inPn_512_863.
    rewrite piu_zz_inPn_512_862.
    rewrite piu_zz_inPn_512_861.
    rewrite piu_zz_inPn_512_860.
    rewrite piu_zz_inPn_512_859.
    rewrite piu_zz_inPn_512_858.
    rewrite piu_zz_inPn_512_857.
    rewrite piu_zz_inPn_512_856.
    rewrite piu_zz_inPn_512_855.
    rewrite piu_zz_inPn_512_854.
    rewrite piu_zz_inPn_512_853.
    rewrite piu_zz_inPn_512_852.
    rewrite piu_zz_inPn_512_851.
    rewrite piu_zz_inPn_512_850.
    rewrite piu_zz_inPn_512_849.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb11 : piu_zz_zprod_seg 512%nat (512%nat + 320%nat) 16%nat = ((if zz_in_Pn 512 833%nat then Z.of_nat 833%nat else 1%Z) * ((if zz_in_Pn 512 834%nat then Z.of_nat 834%nat else 1%Z) * ((if zz_in_Pn 512 835%nat then Z.of_nat 835%nat else 1%Z) * ((if zz_in_Pn 512 836%nat then Z.of_nat 836%nat else 1%Z) * ((if zz_in_Pn 512 837%nat then Z.of_nat 837%nat else 1%Z) * ((if zz_in_Pn 512 838%nat then Z.of_nat 838%nat else 1%Z) * ((if zz_in_Pn 512 839%nat then Z.of_nat 839%nat else 1%Z) * ((if zz_in_Pn 512 840%nat then Z.of_nat 840%nat else 1%Z) * ((if zz_in_Pn 512 841%nat then Z.of_nat 841%nat else 1%Z) * ((if zz_in_Pn 512 842%nat then Z.of_nat 842%nat else 1%Z) * ((if zz_in_Pn 512 843%nat then Z.of_nat 843%nat else 1%Z) * ((if zz_in_Pn 512 844%nat then Z.of_nat 844%nat else 1%Z) * ((if zz_in_Pn 512 845%nat then Z.of_nat 845%nat else 1%Z) * ((if zz_in_Pn 512 846%nat then Z.of_nat 846%nat else 1%Z) * ((if zz_in_Pn 512 847%nat then Z.of_nat 847%nat else 1%Z) * (if zz_in_Pn 512 848%nat then Z.of_nat 848%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_848.
    rewrite piu_zz_inPn_512_847.
    rewrite piu_zz_inPn_512_846.
    rewrite piu_zz_inPn_512_845.
    rewrite piu_zz_inPn_512_844.
    rewrite piu_zz_inPn_512_843.
    rewrite piu_zz_inPn_512_842.
    rewrite piu_zz_inPn_512_841.
    rewrite piu_zz_inPn_512_840.
    rewrite piu_zz_inPn_512_839.
    rewrite piu_zz_inPn_512_838.
    rewrite piu_zz_inPn_512_837.
    rewrite piu_zz_inPn_512_836.
    rewrite piu_zz_inPn_512_835.
    rewrite piu_zz_inPn_512_834.
    rewrite piu_zz_inPn_512_833.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb12 : piu_zz_zprod_seg 512%nat (512%nat + 304%nat) 16%nat = ((if zz_in_Pn 512 817%nat then Z.of_nat 817%nat else 1%Z) * ((if zz_in_Pn 512 818%nat then Z.of_nat 818%nat else 1%Z) * ((if zz_in_Pn 512 819%nat then Z.of_nat 819%nat else 1%Z) * ((if zz_in_Pn 512 820%nat then Z.of_nat 820%nat else 1%Z) * ((if zz_in_Pn 512 821%nat then Z.of_nat 821%nat else 1%Z) * ((if zz_in_Pn 512 822%nat then Z.of_nat 822%nat else 1%Z) * ((if zz_in_Pn 512 823%nat then Z.of_nat 823%nat else 1%Z) * ((if zz_in_Pn 512 824%nat then Z.of_nat 824%nat else 1%Z) * ((if zz_in_Pn 512 825%nat then Z.of_nat 825%nat else 1%Z) * ((if zz_in_Pn 512 826%nat then Z.of_nat 826%nat else 1%Z) * ((if zz_in_Pn 512 827%nat then Z.of_nat 827%nat else 1%Z) * ((if zz_in_Pn 512 828%nat then Z.of_nat 828%nat else 1%Z) * ((if zz_in_Pn 512 829%nat then Z.of_nat 829%nat else 1%Z) * ((if zz_in_Pn 512 830%nat then Z.of_nat 830%nat else 1%Z) * ((if zz_in_Pn 512 831%nat then Z.of_nat 831%nat else 1%Z) * (if zz_in_Pn 512 832%nat then Z.of_nat 832%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_832.
    rewrite piu_zz_inPn_512_831.
    rewrite piu_zz_inPn_512_830.
    rewrite piu_zz_inPn_512_829.
    rewrite piu_zz_inPn_512_828.
    rewrite piu_zz_inPn_512_827.
    rewrite piu_zz_inPn_512_826.
    rewrite piu_zz_inPn_512_825.
    rewrite piu_zz_inPn_512_824.
    rewrite piu_zz_inPn_512_823.
    rewrite piu_zz_inPn_512_822.
    rewrite piu_zz_inPn_512_821.
    rewrite piu_zz_inPn_512_820.
    rewrite piu_zz_inPn_512_819.
    rewrite piu_zz_inPn_512_818.
    rewrite piu_zz_inPn_512_817.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb13 : piu_zz_zprod_seg 512%nat (512%nat + 288%nat) 16%nat = ((if zz_in_Pn 512 801%nat then Z.of_nat 801%nat else 1%Z) * ((if zz_in_Pn 512 802%nat then Z.of_nat 802%nat else 1%Z) * ((if zz_in_Pn 512 803%nat then Z.of_nat 803%nat else 1%Z) * ((if zz_in_Pn 512 804%nat then Z.of_nat 804%nat else 1%Z) * ((if zz_in_Pn 512 805%nat then Z.of_nat 805%nat else 1%Z) * ((if zz_in_Pn 512 806%nat then Z.of_nat 806%nat else 1%Z) * ((if zz_in_Pn 512 807%nat then Z.of_nat 807%nat else 1%Z) * ((if zz_in_Pn 512 808%nat then Z.of_nat 808%nat else 1%Z) * ((if zz_in_Pn 512 809%nat then Z.of_nat 809%nat else 1%Z) * ((if zz_in_Pn 512 810%nat then Z.of_nat 810%nat else 1%Z) * ((if zz_in_Pn 512 811%nat then Z.of_nat 811%nat else 1%Z) * ((if zz_in_Pn 512 812%nat then Z.of_nat 812%nat else 1%Z) * ((if zz_in_Pn 512 813%nat then Z.of_nat 813%nat else 1%Z) * ((if zz_in_Pn 512 814%nat then Z.of_nat 814%nat else 1%Z) * ((if zz_in_Pn 512 815%nat then Z.of_nat 815%nat else 1%Z) * (if zz_in_Pn 512 816%nat then Z.of_nat 816%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_816.
    rewrite piu_zz_inPn_512_815.
    rewrite piu_zz_inPn_512_814.
    rewrite piu_zz_inPn_512_813.
    rewrite piu_zz_inPn_512_812.
    rewrite piu_zz_inPn_512_811.
    rewrite piu_zz_inPn_512_810.
    rewrite piu_zz_inPn_512_809.
    rewrite piu_zz_inPn_512_808.
    rewrite piu_zz_inPn_512_807.
    rewrite piu_zz_inPn_512_806.
    rewrite piu_zz_inPn_512_805.
    rewrite piu_zz_inPn_512_804.
    rewrite piu_zz_inPn_512_803.
    rewrite piu_zz_inPn_512_802.
    rewrite piu_zz_inPn_512_801.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb14 : piu_zz_zprod_seg 512%nat (512%nat + 272%nat) 16%nat = ((if zz_in_Pn 512 785%nat then Z.of_nat 785%nat else 1%Z) * ((if zz_in_Pn 512 786%nat then Z.of_nat 786%nat else 1%Z) * ((if zz_in_Pn 512 787%nat then Z.of_nat 787%nat else 1%Z) * ((if zz_in_Pn 512 788%nat then Z.of_nat 788%nat else 1%Z) * ((if zz_in_Pn 512 789%nat then Z.of_nat 789%nat else 1%Z) * ((if zz_in_Pn 512 790%nat then Z.of_nat 790%nat else 1%Z) * ((if zz_in_Pn 512 791%nat then Z.of_nat 791%nat else 1%Z) * ((if zz_in_Pn 512 792%nat then Z.of_nat 792%nat else 1%Z) * ((if zz_in_Pn 512 793%nat then Z.of_nat 793%nat else 1%Z) * ((if zz_in_Pn 512 794%nat then Z.of_nat 794%nat else 1%Z) * ((if zz_in_Pn 512 795%nat then Z.of_nat 795%nat else 1%Z) * ((if zz_in_Pn 512 796%nat then Z.of_nat 796%nat else 1%Z) * ((if zz_in_Pn 512 797%nat then Z.of_nat 797%nat else 1%Z) * ((if zz_in_Pn 512 798%nat then Z.of_nat 798%nat else 1%Z) * ((if zz_in_Pn 512 799%nat then Z.of_nat 799%nat else 1%Z) * (if zz_in_Pn 512 800%nat then Z.of_nat 800%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_800.
    rewrite piu_zz_inPn_512_799.
    rewrite piu_zz_inPn_512_798.
    rewrite piu_zz_inPn_512_797.
    rewrite piu_zz_inPn_512_796.
    rewrite piu_zz_inPn_512_795.
    rewrite piu_zz_inPn_512_794.
    rewrite piu_zz_inPn_512_793.
    rewrite piu_zz_inPn_512_792.
    rewrite piu_zz_inPn_512_791.
    rewrite piu_zz_inPn_512_790.
    rewrite piu_zz_inPn_512_789.
    rewrite piu_zz_inPn_512_788.
    rewrite piu_zz_inPn_512_787.
    rewrite piu_zz_inPn_512_786.
    rewrite piu_zz_inPn_512_785.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb15 : piu_zz_zprod_seg 512%nat (512%nat + 256%nat) 16%nat = ((if zz_in_Pn 512 769%nat then Z.of_nat 769%nat else 1%Z) * ((if zz_in_Pn 512 770%nat then Z.of_nat 770%nat else 1%Z) * ((if zz_in_Pn 512 771%nat then Z.of_nat 771%nat else 1%Z) * ((if zz_in_Pn 512 772%nat then Z.of_nat 772%nat else 1%Z) * ((if zz_in_Pn 512 773%nat then Z.of_nat 773%nat else 1%Z) * ((if zz_in_Pn 512 774%nat then Z.of_nat 774%nat else 1%Z) * ((if zz_in_Pn 512 775%nat then Z.of_nat 775%nat else 1%Z) * ((if zz_in_Pn 512 776%nat then Z.of_nat 776%nat else 1%Z) * ((if zz_in_Pn 512 777%nat then Z.of_nat 777%nat else 1%Z) * ((if zz_in_Pn 512 778%nat then Z.of_nat 778%nat else 1%Z) * ((if zz_in_Pn 512 779%nat then Z.of_nat 779%nat else 1%Z) * ((if zz_in_Pn 512 780%nat then Z.of_nat 780%nat else 1%Z) * ((if zz_in_Pn 512 781%nat then Z.of_nat 781%nat else 1%Z) * ((if zz_in_Pn 512 782%nat then Z.of_nat 782%nat else 1%Z) * ((if zz_in_Pn 512 783%nat then Z.of_nat 783%nat else 1%Z) * (if zz_in_Pn 512 784%nat then Z.of_nat 784%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_784.
    rewrite piu_zz_inPn_512_783.
    rewrite piu_zz_inPn_512_782.
    rewrite piu_zz_inPn_512_781.
    rewrite piu_zz_inPn_512_780.
    rewrite piu_zz_inPn_512_779.
    rewrite piu_zz_inPn_512_778.
    rewrite piu_zz_inPn_512_777.
    rewrite piu_zz_inPn_512_776.
    rewrite piu_zz_inPn_512_775.
    rewrite piu_zz_inPn_512_774.
    rewrite piu_zz_inPn_512_773.
    rewrite piu_zz_inPn_512_772.
    rewrite piu_zz_inPn_512_771.
    rewrite piu_zz_inPn_512_770.
    rewrite piu_zz_inPn_512_769.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb16 : piu_zz_zprod_seg 512%nat (512%nat + 240%nat) 16%nat = ((if zz_in_Pn 512 753%nat then Z.of_nat 753%nat else 1%Z) * ((if zz_in_Pn 512 754%nat then Z.of_nat 754%nat else 1%Z) * ((if zz_in_Pn 512 755%nat then Z.of_nat 755%nat else 1%Z) * ((if zz_in_Pn 512 756%nat then Z.of_nat 756%nat else 1%Z) * ((if zz_in_Pn 512 757%nat then Z.of_nat 757%nat else 1%Z) * ((if zz_in_Pn 512 758%nat then Z.of_nat 758%nat else 1%Z) * ((if zz_in_Pn 512 759%nat then Z.of_nat 759%nat else 1%Z) * ((if zz_in_Pn 512 760%nat then Z.of_nat 760%nat else 1%Z) * ((if zz_in_Pn 512 761%nat then Z.of_nat 761%nat else 1%Z) * ((if zz_in_Pn 512 762%nat then Z.of_nat 762%nat else 1%Z) * ((if zz_in_Pn 512 763%nat then Z.of_nat 763%nat else 1%Z) * ((if zz_in_Pn 512 764%nat then Z.of_nat 764%nat else 1%Z) * ((if zz_in_Pn 512 765%nat then Z.of_nat 765%nat else 1%Z) * ((if zz_in_Pn 512 766%nat then Z.of_nat 766%nat else 1%Z) * ((if zz_in_Pn 512 767%nat then Z.of_nat 767%nat else 1%Z) * (if zz_in_Pn 512 768%nat then Z.of_nat 768%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_768.
    rewrite piu_zz_inPn_512_767.
    rewrite piu_zz_inPn_512_766.
    rewrite piu_zz_inPn_512_765.
    rewrite piu_zz_inPn_512_764.
    rewrite piu_zz_inPn_512_763.
    rewrite piu_zz_inPn_512_762.
    rewrite piu_zz_inPn_512_761.
    rewrite piu_zz_inPn_512_760.
    rewrite piu_zz_inPn_512_759.
    rewrite piu_zz_inPn_512_758.
    rewrite piu_zz_inPn_512_757.
    rewrite piu_zz_inPn_512_756.
    rewrite piu_zz_inPn_512_755.
    rewrite piu_zz_inPn_512_754.
    rewrite piu_zz_inPn_512_753.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb17 : piu_zz_zprod_seg 512%nat (512%nat + 224%nat) 16%nat = ((if zz_in_Pn 512 737%nat then Z.of_nat 737%nat else 1%Z) * ((if zz_in_Pn 512 738%nat then Z.of_nat 738%nat else 1%Z) * ((if zz_in_Pn 512 739%nat then Z.of_nat 739%nat else 1%Z) * ((if zz_in_Pn 512 740%nat then Z.of_nat 740%nat else 1%Z) * ((if zz_in_Pn 512 741%nat then Z.of_nat 741%nat else 1%Z) * ((if zz_in_Pn 512 742%nat then Z.of_nat 742%nat else 1%Z) * ((if zz_in_Pn 512 743%nat then Z.of_nat 743%nat else 1%Z) * ((if zz_in_Pn 512 744%nat then Z.of_nat 744%nat else 1%Z) * ((if zz_in_Pn 512 745%nat then Z.of_nat 745%nat else 1%Z) * ((if zz_in_Pn 512 746%nat then Z.of_nat 746%nat else 1%Z) * ((if zz_in_Pn 512 747%nat then Z.of_nat 747%nat else 1%Z) * ((if zz_in_Pn 512 748%nat then Z.of_nat 748%nat else 1%Z) * ((if zz_in_Pn 512 749%nat then Z.of_nat 749%nat else 1%Z) * ((if zz_in_Pn 512 750%nat then Z.of_nat 750%nat else 1%Z) * ((if zz_in_Pn 512 751%nat then Z.of_nat 751%nat else 1%Z) * (if zz_in_Pn 512 752%nat then Z.of_nat 752%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_752.
    rewrite piu_zz_inPn_512_751.
    rewrite piu_zz_inPn_512_750.
    rewrite piu_zz_inPn_512_749.
    rewrite piu_zz_inPn_512_748.
    rewrite piu_zz_inPn_512_747.
    rewrite piu_zz_inPn_512_746.
    rewrite piu_zz_inPn_512_745.
    rewrite piu_zz_inPn_512_744.
    rewrite piu_zz_inPn_512_743.
    rewrite piu_zz_inPn_512_742.
    rewrite piu_zz_inPn_512_741.
    rewrite piu_zz_inPn_512_740.
    rewrite piu_zz_inPn_512_739.
    rewrite piu_zz_inPn_512_738.
    rewrite piu_zz_inPn_512_737.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb18 : piu_zz_zprod_seg 512%nat (512%nat + 208%nat) 16%nat = ((if zz_in_Pn 512 721%nat then Z.of_nat 721%nat else 1%Z) * ((if zz_in_Pn 512 722%nat then Z.of_nat 722%nat else 1%Z) * ((if zz_in_Pn 512 723%nat then Z.of_nat 723%nat else 1%Z) * ((if zz_in_Pn 512 724%nat then Z.of_nat 724%nat else 1%Z) * ((if zz_in_Pn 512 725%nat then Z.of_nat 725%nat else 1%Z) * ((if zz_in_Pn 512 726%nat then Z.of_nat 726%nat else 1%Z) * ((if zz_in_Pn 512 727%nat then Z.of_nat 727%nat else 1%Z) * ((if zz_in_Pn 512 728%nat then Z.of_nat 728%nat else 1%Z) * ((if zz_in_Pn 512 729%nat then Z.of_nat 729%nat else 1%Z) * ((if zz_in_Pn 512 730%nat then Z.of_nat 730%nat else 1%Z) * ((if zz_in_Pn 512 731%nat then Z.of_nat 731%nat else 1%Z) * ((if zz_in_Pn 512 732%nat then Z.of_nat 732%nat else 1%Z) * ((if zz_in_Pn 512 733%nat then Z.of_nat 733%nat else 1%Z) * ((if zz_in_Pn 512 734%nat then Z.of_nat 734%nat else 1%Z) * ((if zz_in_Pn 512 735%nat then Z.of_nat 735%nat else 1%Z) * (if zz_in_Pn 512 736%nat then Z.of_nat 736%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_736.
    rewrite piu_zz_inPn_512_735.
    rewrite piu_zz_inPn_512_734.
    rewrite piu_zz_inPn_512_733.
    rewrite piu_zz_inPn_512_732.
    rewrite piu_zz_inPn_512_731.
    rewrite piu_zz_inPn_512_730.
    rewrite piu_zz_inPn_512_729.
    rewrite piu_zz_inPn_512_728.
    rewrite piu_zz_inPn_512_727.
    rewrite piu_zz_inPn_512_726.
    rewrite piu_zz_inPn_512_725.
    rewrite piu_zz_inPn_512_724.
    rewrite piu_zz_inPn_512_723.
    rewrite piu_zz_inPn_512_722.
    rewrite piu_zz_inPn_512_721.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb19 : piu_zz_zprod_seg 512%nat (512%nat + 192%nat) 16%nat = ((if zz_in_Pn 512 705%nat then Z.of_nat 705%nat else 1%Z) * ((if zz_in_Pn 512 706%nat then Z.of_nat 706%nat else 1%Z) * ((if zz_in_Pn 512 707%nat then Z.of_nat 707%nat else 1%Z) * ((if zz_in_Pn 512 708%nat then Z.of_nat 708%nat else 1%Z) * ((if zz_in_Pn 512 709%nat then Z.of_nat 709%nat else 1%Z) * ((if zz_in_Pn 512 710%nat then Z.of_nat 710%nat else 1%Z) * ((if zz_in_Pn 512 711%nat then Z.of_nat 711%nat else 1%Z) * ((if zz_in_Pn 512 712%nat then Z.of_nat 712%nat else 1%Z) * ((if zz_in_Pn 512 713%nat then Z.of_nat 713%nat else 1%Z) * ((if zz_in_Pn 512 714%nat then Z.of_nat 714%nat else 1%Z) * ((if zz_in_Pn 512 715%nat then Z.of_nat 715%nat else 1%Z) * ((if zz_in_Pn 512 716%nat then Z.of_nat 716%nat else 1%Z) * ((if zz_in_Pn 512 717%nat then Z.of_nat 717%nat else 1%Z) * ((if zz_in_Pn 512 718%nat then Z.of_nat 718%nat else 1%Z) * ((if zz_in_Pn 512 719%nat then Z.of_nat 719%nat else 1%Z) * (if zz_in_Pn 512 720%nat then Z.of_nat 720%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_720.
    rewrite piu_zz_inPn_512_719.
    rewrite piu_zz_inPn_512_718.
    rewrite piu_zz_inPn_512_717.
    rewrite piu_zz_inPn_512_716.
    rewrite piu_zz_inPn_512_715.
    rewrite piu_zz_inPn_512_714.
    rewrite piu_zz_inPn_512_713.
    rewrite piu_zz_inPn_512_712.
    rewrite piu_zz_inPn_512_711.
    rewrite piu_zz_inPn_512_710.
    rewrite piu_zz_inPn_512_709.
    rewrite piu_zz_inPn_512_708.
    rewrite piu_zz_inPn_512_707.
    rewrite piu_zz_inPn_512_706.
    rewrite piu_zz_inPn_512_705.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb20 : piu_zz_zprod_seg 512%nat (512%nat + 176%nat) 16%nat = ((if zz_in_Pn 512 689%nat then Z.of_nat 689%nat else 1%Z) * ((if zz_in_Pn 512 690%nat then Z.of_nat 690%nat else 1%Z) * ((if zz_in_Pn 512 691%nat then Z.of_nat 691%nat else 1%Z) * ((if zz_in_Pn 512 692%nat then Z.of_nat 692%nat else 1%Z) * ((if zz_in_Pn 512 693%nat then Z.of_nat 693%nat else 1%Z) * ((if zz_in_Pn 512 694%nat then Z.of_nat 694%nat else 1%Z) * ((if zz_in_Pn 512 695%nat then Z.of_nat 695%nat else 1%Z) * ((if zz_in_Pn 512 696%nat then Z.of_nat 696%nat else 1%Z) * ((if zz_in_Pn 512 697%nat then Z.of_nat 697%nat else 1%Z) * ((if zz_in_Pn 512 698%nat then Z.of_nat 698%nat else 1%Z) * ((if zz_in_Pn 512 699%nat then Z.of_nat 699%nat else 1%Z) * ((if zz_in_Pn 512 700%nat then Z.of_nat 700%nat else 1%Z) * ((if zz_in_Pn 512 701%nat then Z.of_nat 701%nat else 1%Z) * ((if zz_in_Pn 512 702%nat then Z.of_nat 702%nat else 1%Z) * ((if zz_in_Pn 512 703%nat then Z.of_nat 703%nat else 1%Z) * (if zz_in_Pn 512 704%nat then Z.of_nat 704%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_704.
    rewrite piu_zz_inPn_512_703.
    rewrite piu_zz_inPn_512_702.
    rewrite piu_zz_inPn_512_701.
    rewrite piu_zz_inPn_512_700.
    rewrite piu_zz_inPn_512_699.
    rewrite piu_zz_inPn_512_698.
    rewrite piu_zz_inPn_512_697.
    rewrite piu_zz_inPn_512_696.
    rewrite piu_zz_inPn_512_695.
    rewrite piu_zz_inPn_512_694.
    rewrite piu_zz_inPn_512_693.
    rewrite piu_zz_inPn_512_692.
    rewrite piu_zz_inPn_512_691.
    rewrite piu_zz_inPn_512_690.
    rewrite piu_zz_inPn_512_689.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb21 : piu_zz_zprod_seg 512%nat (512%nat + 160%nat) 16%nat = ((if zz_in_Pn 512 673%nat then Z.of_nat 673%nat else 1%Z) * ((if zz_in_Pn 512 674%nat then Z.of_nat 674%nat else 1%Z) * ((if zz_in_Pn 512 675%nat then Z.of_nat 675%nat else 1%Z) * ((if zz_in_Pn 512 676%nat then Z.of_nat 676%nat else 1%Z) * ((if zz_in_Pn 512 677%nat then Z.of_nat 677%nat else 1%Z) * ((if zz_in_Pn 512 678%nat then Z.of_nat 678%nat else 1%Z) * ((if zz_in_Pn 512 679%nat then Z.of_nat 679%nat else 1%Z) * ((if zz_in_Pn 512 680%nat then Z.of_nat 680%nat else 1%Z) * ((if zz_in_Pn 512 681%nat then Z.of_nat 681%nat else 1%Z) * ((if zz_in_Pn 512 682%nat then Z.of_nat 682%nat else 1%Z) * ((if zz_in_Pn 512 683%nat then Z.of_nat 683%nat else 1%Z) * ((if zz_in_Pn 512 684%nat then Z.of_nat 684%nat else 1%Z) * ((if zz_in_Pn 512 685%nat then Z.of_nat 685%nat else 1%Z) * ((if zz_in_Pn 512 686%nat then Z.of_nat 686%nat else 1%Z) * ((if zz_in_Pn 512 687%nat then Z.of_nat 687%nat else 1%Z) * (if zz_in_Pn 512 688%nat then Z.of_nat 688%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_688.
    rewrite piu_zz_inPn_512_687.
    rewrite piu_zz_inPn_512_686.
    rewrite piu_zz_inPn_512_685.
    rewrite piu_zz_inPn_512_684.
    rewrite piu_zz_inPn_512_683.
    rewrite piu_zz_inPn_512_682.
    rewrite piu_zz_inPn_512_681.
    rewrite piu_zz_inPn_512_680.
    rewrite piu_zz_inPn_512_679.
    rewrite piu_zz_inPn_512_678.
    rewrite piu_zz_inPn_512_677.
    rewrite piu_zz_inPn_512_676.
    rewrite piu_zz_inPn_512_675.
    rewrite piu_zz_inPn_512_674.
    rewrite piu_zz_inPn_512_673.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb22 : piu_zz_zprod_seg 512%nat (512%nat + 144%nat) 16%nat = ((if zz_in_Pn 512 657%nat then Z.of_nat 657%nat else 1%Z) * ((if zz_in_Pn 512 658%nat then Z.of_nat 658%nat else 1%Z) * ((if zz_in_Pn 512 659%nat then Z.of_nat 659%nat else 1%Z) * ((if zz_in_Pn 512 660%nat then Z.of_nat 660%nat else 1%Z) * ((if zz_in_Pn 512 661%nat then Z.of_nat 661%nat else 1%Z) * ((if zz_in_Pn 512 662%nat then Z.of_nat 662%nat else 1%Z) * ((if zz_in_Pn 512 663%nat then Z.of_nat 663%nat else 1%Z) * ((if zz_in_Pn 512 664%nat then Z.of_nat 664%nat else 1%Z) * ((if zz_in_Pn 512 665%nat then Z.of_nat 665%nat else 1%Z) * ((if zz_in_Pn 512 666%nat then Z.of_nat 666%nat else 1%Z) * ((if zz_in_Pn 512 667%nat then Z.of_nat 667%nat else 1%Z) * ((if zz_in_Pn 512 668%nat then Z.of_nat 668%nat else 1%Z) * ((if zz_in_Pn 512 669%nat then Z.of_nat 669%nat else 1%Z) * ((if zz_in_Pn 512 670%nat then Z.of_nat 670%nat else 1%Z) * ((if zz_in_Pn 512 671%nat then Z.of_nat 671%nat else 1%Z) * (if zz_in_Pn 512 672%nat then Z.of_nat 672%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_672.
    rewrite piu_zz_inPn_512_671.
    rewrite piu_zz_inPn_512_670.
    rewrite piu_zz_inPn_512_669.
    rewrite piu_zz_inPn_512_668.
    rewrite piu_zz_inPn_512_667.
    rewrite piu_zz_inPn_512_666.
    rewrite piu_zz_inPn_512_665.
    rewrite piu_zz_inPn_512_664.
    rewrite piu_zz_inPn_512_663.
    rewrite piu_zz_inPn_512_662.
    rewrite piu_zz_inPn_512_661.
    rewrite piu_zz_inPn_512_660.
    rewrite piu_zz_inPn_512_659.
    rewrite piu_zz_inPn_512_658.
    rewrite piu_zz_inPn_512_657.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb23 : piu_zz_zprod_seg 512%nat (512%nat + 128%nat) 16%nat = ((if zz_in_Pn 512 641%nat then Z.of_nat 641%nat else 1%Z) * ((if zz_in_Pn 512 642%nat then Z.of_nat 642%nat else 1%Z) * ((if zz_in_Pn 512 643%nat then Z.of_nat 643%nat else 1%Z) * ((if zz_in_Pn 512 644%nat then Z.of_nat 644%nat else 1%Z) * ((if zz_in_Pn 512 645%nat then Z.of_nat 645%nat else 1%Z) * ((if zz_in_Pn 512 646%nat then Z.of_nat 646%nat else 1%Z) * ((if zz_in_Pn 512 647%nat then Z.of_nat 647%nat else 1%Z) * ((if zz_in_Pn 512 648%nat then Z.of_nat 648%nat else 1%Z) * ((if zz_in_Pn 512 649%nat then Z.of_nat 649%nat else 1%Z) * ((if zz_in_Pn 512 650%nat then Z.of_nat 650%nat else 1%Z) * ((if zz_in_Pn 512 651%nat then Z.of_nat 651%nat else 1%Z) * ((if zz_in_Pn 512 652%nat then Z.of_nat 652%nat else 1%Z) * ((if zz_in_Pn 512 653%nat then Z.of_nat 653%nat else 1%Z) * ((if zz_in_Pn 512 654%nat then Z.of_nat 654%nat else 1%Z) * ((if zz_in_Pn 512 655%nat then Z.of_nat 655%nat else 1%Z) * (if zz_in_Pn 512 656%nat then Z.of_nat 656%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_656.
    rewrite piu_zz_inPn_512_655.
    rewrite piu_zz_inPn_512_654.
    rewrite piu_zz_inPn_512_653.
    rewrite piu_zz_inPn_512_652.
    rewrite piu_zz_inPn_512_651.
    rewrite piu_zz_inPn_512_650.
    rewrite piu_zz_inPn_512_649.
    rewrite piu_zz_inPn_512_648.
    rewrite piu_zz_inPn_512_647.
    rewrite piu_zz_inPn_512_646.
    rewrite piu_zz_inPn_512_645.
    rewrite piu_zz_inPn_512_644.
    rewrite piu_zz_inPn_512_643.
    rewrite piu_zz_inPn_512_642.
    rewrite piu_zz_inPn_512_641.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb24 : piu_zz_zprod_seg 512%nat (512%nat + 112%nat) 16%nat = ((if zz_in_Pn 512 625%nat then Z.of_nat 625%nat else 1%Z) * ((if zz_in_Pn 512 626%nat then Z.of_nat 626%nat else 1%Z) * ((if zz_in_Pn 512 627%nat then Z.of_nat 627%nat else 1%Z) * ((if zz_in_Pn 512 628%nat then Z.of_nat 628%nat else 1%Z) * ((if zz_in_Pn 512 629%nat then Z.of_nat 629%nat else 1%Z) * ((if zz_in_Pn 512 630%nat then Z.of_nat 630%nat else 1%Z) * ((if zz_in_Pn 512 631%nat then Z.of_nat 631%nat else 1%Z) * ((if zz_in_Pn 512 632%nat then Z.of_nat 632%nat else 1%Z) * ((if zz_in_Pn 512 633%nat then Z.of_nat 633%nat else 1%Z) * ((if zz_in_Pn 512 634%nat then Z.of_nat 634%nat else 1%Z) * ((if zz_in_Pn 512 635%nat then Z.of_nat 635%nat else 1%Z) * ((if zz_in_Pn 512 636%nat then Z.of_nat 636%nat else 1%Z) * ((if zz_in_Pn 512 637%nat then Z.of_nat 637%nat else 1%Z) * ((if zz_in_Pn 512 638%nat then Z.of_nat 638%nat else 1%Z) * ((if zz_in_Pn 512 639%nat then Z.of_nat 639%nat else 1%Z) * (if zz_in_Pn 512 640%nat then Z.of_nat 640%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_640.
    rewrite piu_zz_inPn_512_639.
    rewrite piu_zz_inPn_512_638.
    rewrite piu_zz_inPn_512_637.
    rewrite piu_zz_inPn_512_636.
    rewrite piu_zz_inPn_512_635.
    rewrite piu_zz_inPn_512_634.
    rewrite piu_zz_inPn_512_633.
    rewrite piu_zz_inPn_512_632.
    rewrite piu_zz_inPn_512_631.
    rewrite piu_zz_inPn_512_630.
    rewrite piu_zz_inPn_512_629.
    rewrite piu_zz_inPn_512_628.
    rewrite piu_zz_inPn_512_627.
    rewrite piu_zz_inPn_512_626.
    rewrite piu_zz_inPn_512_625.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb25 : piu_zz_zprod_seg 512%nat (512%nat + 96%nat) 16%nat = ((if zz_in_Pn 512 609%nat then Z.of_nat 609%nat else 1%Z) * ((if zz_in_Pn 512 610%nat then Z.of_nat 610%nat else 1%Z) * ((if zz_in_Pn 512 611%nat then Z.of_nat 611%nat else 1%Z) * ((if zz_in_Pn 512 612%nat then Z.of_nat 612%nat else 1%Z) * ((if zz_in_Pn 512 613%nat then Z.of_nat 613%nat else 1%Z) * ((if zz_in_Pn 512 614%nat then Z.of_nat 614%nat else 1%Z) * ((if zz_in_Pn 512 615%nat then Z.of_nat 615%nat else 1%Z) * ((if zz_in_Pn 512 616%nat then Z.of_nat 616%nat else 1%Z) * ((if zz_in_Pn 512 617%nat then Z.of_nat 617%nat else 1%Z) * ((if zz_in_Pn 512 618%nat then Z.of_nat 618%nat else 1%Z) * ((if zz_in_Pn 512 619%nat then Z.of_nat 619%nat else 1%Z) * ((if zz_in_Pn 512 620%nat then Z.of_nat 620%nat else 1%Z) * ((if zz_in_Pn 512 621%nat then Z.of_nat 621%nat else 1%Z) * ((if zz_in_Pn 512 622%nat then Z.of_nat 622%nat else 1%Z) * ((if zz_in_Pn 512 623%nat then Z.of_nat 623%nat else 1%Z) * (if zz_in_Pn 512 624%nat then Z.of_nat 624%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_624.
    rewrite piu_zz_inPn_512_623.
    rewrite piu_zz_inPn_512_622.
    rewrite piu_zz_inPn_512_621.
    rewrite piu_zz_inPn_512_620.
    rewrite piu_zz_inPn_512_619.
    rewrite piu_zz_inPn_512_618.
    rewrite piu_zz_inPn_512_617.
    rewrite piu_zz_inPn_512_616.
    rewrite piu_zz_inPn_512_615.
    rewrite piu_zz_inPn_512_614.
    rewrite piu_zz_inPn_512_613.
    rewrite piu_zz_inPn_512_612.
    rewrite piu_zz_inPn_512_611.
    rewrite piu_zz_inPn_512_610.
    rewrite piu_zz_inPn_512_609.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb26 : piu_zz_zprod_seg 512%nat (512%nat + 80%nat) 16%nat = ((if zz_in_Pn 512 593%nat then Z.of_nat 593%nat else 1%Z) * ((if zz_in_Pn 512 594%nat then Z.of_nat 594%nat else 1%Z) * ((if zz_in_Pn 512 595%nat then Z.of_nat 595%nat else 1%Z) * ((if zz_in_Pn 512 596%nat then Z.of_nat 596%nat else 1%Z) * ((if zz_in_Pn 512 597%nat then Z.of_nat 597%nat else 1%Z) * ((if zz_in_Pn 512 598%nat then Z.of_nat 598%nat else 1%Z) * ((if zz_in_Pn 512 599%nat then Z.of_nat 599%nat else 1%Z) * ((if zz_in_Pn 512 600%nat then Z.of_nat 600%nat else 1%Z) * ((if zz_in_Pn 512 601%nat then Z.of_nat 601%nat else 1%Z) * ((if zz_in_Pn 512 602%nat then Z.of_nat 602%nat else 1%Z) * ((if zz_in_Pn 512 603%nat then Z.of_nat 603%nat else 1%Z) * ((if zz_in_Pn 512 604%nat then Z.of_nat 604%nat else 1%Z) * ((if zz_in_Pn 512 605%nat then Z.of_nat 605%nat else 1%Z) * ((if zz_in_Pn 512 606%nat then Z.of_nat 606%nat else 1%Z) * ((if zz_in_Pn 512 607%nat then Z.of_nat 607%nat else 1%Z) * (if zz_in_Pn 512 608%nat then Z.of_nat 608%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_608.
    rewrite piu_zz_inPn_512_607.
    rewrite piu_zz_inPn_512_606.
    rewrite piu_zz_inPn_512_605.
    rewrite piu_zz_inPn_512_604.
    rewrite piu_zz_inPn_512_603.
    rewrite piu_zz_inPn_512_602.
    rewrite piu_zz_inPn_512_601.
    rewrite piu_zz_inPn_512_600.
    rewrite piu_zz_inPn_512_599.
    rewrite piu_zz_inPn_512_598.
    rewrite piu_zz_inPn_512_597.
    rewrite piu_zz_inPn_512_596.
    rewrite piu_zz_inPn_512_595.
    rewrite piu_zz_inPn_512_594.
    rewrite piu_zz_inPn_512_593.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb27 : piu_zz_zprod_seg 512%nat (512%nat + 64%nat) 16%nat = ((if zz_in_Pn 512 577%nat then Z.of_nat 577%nat else 1%Z) * ((if zz_in_Pn 512 578%nat then Z.of_nat 578%nat else 1%Z) * ((if zz_in_Pn 512 579%nat then Z.of_nat 579%nat else 1%Z) * ((if zz_in_Pn 512 580%nat then Z.of_nat 580%nat else 1%Z) * ((if zz_in_Pn 512 581%nat then Z.of_nat 581%nat else 1%Z) * ((if zz_in_Pn 512 582%nat then Z.of_nat 582%nat else 1%Z) * ((if zz_in_Pn 512 583%nat then Z.of_nat 583%nat else 1%Z) * ((if zz_in_Pn 512 584%nat then Z.of_nat 584%nat else 1%Z) * ((if zz_in_Pn 512 585%nat then Z.of_nat 585%nat else 1%Z) * ((if zz_in_Pn 512 586%nat then Z.of_nat 586%nat else 1%Z) * ((if zz_in_Pn 512 587%nat then Z.of_nat 587%nat else 1%Z) * ((if zz_in_Pn 512 588%nat then Z.of_nat 588%nat else 1%Z) * ((if zz_in_Pn 512 589%nat then Z.of_nat 589%nat else 1%Z) * ((if zz_in_Pn 512 590%nat then Z.of_nat 590%nat else 1%Z) * ((if zz_in_Pn 512 591%nat then Z.of_nat 591%nat else 1%Z) * (if zz_in_Pn 512 592%nat then Z.of_nat 592%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_592.
    rewrite piu_zz_inPn_512_591.
    rewrite piu_zz_inPn_512_590.
    rewrite piu_zz_inPn_512_589.
    rewrite piu_zz_inPn_512_588.
    rewrite piu_zz_inPn_512_587.
    rewrite piu_zz_inPn_512_586.
    rewrite piu_zz_inPn_512_585.
    rewrite piu_zz_inPn_512_584.
    rewrite piu_zz_inPn_512_583.
    rewrite piu_zz_inPn_512_582.
    rewrite piu_zz_inPn_512_581.
    rewrite piu_zz_inPn_512_580.
    rewrite piu_zz_inPn_512_579.
    rewrite piu_zz_inPn_512_578.
    rewrite piu_zz_inPn_512_577.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb28 : piu_zz_zprod_seg 512%nat (512%nat + 48%nat) 16%nat = ((if zz_in_Pn 512 561%nat then Z.of_nat 561%nat else 1%Z) * ((if zz_in_Pn 512 562%nat then Z.of_nat 562%nat else 1%Z) * ((if zz_in_Pn 512 563%nat then Z.of_nat 563%nat else 1%Z) * ((if zz_in_Pn 512 564%nat then Z.of_nat 564%nat else 1%Z) * ((if zz_in_Pn 512 565%nat then Z.of_nat 565%nat else 1%Z) * ((if zz_in_Pn 512 566%nat then Z.of_nat 566%nat else 1%Z) * ((if zz_in_Pn 512 567%nat then Z.of_nat 567%nat else 1%Z) * ((if zz_in_Pn 512 568%nat then Z.of_nat 568%nat else 1%Z) * ((if zz_in_Pn 512 569%nat then Z.of_nat 569%nat else 1%Z) * ((if zz_in_Pn 512 570%nat then Z.of_nat 570%nat else 1%Z) * ((if zz_in_Pn 512 571%nat then Z.of_nat 571%nat else 1%Z) * ((if zz_in_Pn 512 572%nat then Z.of_nat 572%nat else 1%Z) * ((if zz_in_Pn 512 573%nat then Z.of_nat 573%nat else 1%Z) * ((if zz_in_Pn 512 574%nat then Z.of_nat 574%nat else 1%Z) * ((if zz_in_Pn 512 575%nat then Z.of_nat 575%nat else 1%Z) * (if zz_in_Pn 512 576%nat then Z.of_nat 576%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_576.
    rewrite piu_zz_inPn_512_575.
    rewrite piu_zz_inPn_512_574.
    rewrite piu_zz_inPn_512_573.
    rewrite piu_zz_inPn_512_572.
    rewrite piu_zz_inPn_512_571.
    rewrite piu_zz_inPn_512_570.
    rewrite piu_zz_inPn_512_569.
    rewrite piu_zz_inPn_512_568.
    rewrite piu_zz_inPn_512_567.
    rewrite piu_zz_inPn_512_566.
    rewrite piu_zz_inPn_512_565.
    rewrite piu_zz_inPn_512_564.
    rewrite piu_zz_inPn_512_563.
    rewrite piu_zz_inPn_512_562.
    rewrite piu_zz_inPn_512_561.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb29 : piu_zz_zprod_seg 512%nat (512%nat + 32%nat) 16%nat = ((if zz_in_Pn 512 545%nat then Z.of_nat 545%nat else 1%Z) * ((if zz_in_Pn 512 546%nat then Z.of_nat 546%nat else 1%Z) * ((if zz_in_Pn 512 547%nat then Z.of_nat 547%nat else 1%Z) * ((if zz_in_Pn 512 548%nat then Z.of_nat 548%nat else 1%Z) * ((if zz_in_Pn 512 549%nat then Z.of_nat 549%nat else 1%Z) * ((if zz_in_Pn 512 550%nat then Z.of_nat 550%nat else 1%Z) * ((if zz_in_Pn 512 551%nat then Z.of_nat 551%nat else 1%Z) * ((if zz_in_Pn 512 552%nat then Z.of_nat 552%nat else 1%Z) * ((if zz_in_Pn 512 553%nat then Z.of_nat 553%nat else 1%Z) * ((if zz_in_Pn 512 554%nat then Z.of_nat 554%nat else 1%Z) * ((if zz_in_Pn 512 555%nat then Z.of_nat 555%nat else 1%Z) * ((if zz_in_Pn 512 556%nat then Z.of_nat 556%nat else 1%Z) * ((if zz_in_Pn 512 557%nat then Z.of_nat 557%nat else 1%Z) * ((if zz_in_Pn 512 558%nat then Z.of_nat 558%nat else 1%Z) * ((if zz_in_Pn 512 559%nat then Z.of_nat 559%nat else 1%Z) * (if zz_in_Pn 512 560%nat then Z.of_nat 560%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_560.
    rewrite piu_zz_inPn_512_559.
    rewrite piu_zz_inPn_512_558.
    rewrite piu_zz_inPn_512_557.
    rewrite piu_zz_inPn_512_556.
    rewrite piu_zz_inPn_512_555.
    rewrite piu_zz_inPn_512_554.
    rewrite piu_zz_inPn_512_553.
    rewrite piu_zz_inPn_512_552.
    rewrite piu_zz_inPn_512_551.
    rewrite piu_zz_inPn_512_550.
    rewrite piu_zz_inPn_512_549.
    rewrite piu_zz_inPn_512_548.
    rewrite piu_zz_inPn_512_547.
    rewrite piu_zz_inPn_512_546.
    rewrite piu_zz_inPn_512_545.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb30 : piu_zz_zprod_seg 512%nat (512%nat + 16%nat) 16%nat = ((if zz_in_Pn 512 529%nat then Z.of_nat 529%nat else 1%Z) * ((if zz_in_Pn 512 530%nat then Z.of_nat 530%nat else 1%Z) * ((if zz_in_Pn 512 531%nat then Z.of_nat 531%nat else 1%Z) * ((if zz_in_Pn 512 532%nat then Z.of_nat 532%nat else 1%Z) * ((if zz_in_Pn 512 533%nat then Z.of_nat 533%nat else 1%Z) * ((if zz_in_Pn 512 534%nat then Z.of_nat 534%nat else 1%Z) * ((if zz_in_Pn 512 535%nat then Z.of_nat 535%nat else 1%Z) * ((if zz_in_Pn 512 536%nat then Z.of_nat 536%nat else 1%Z) * ((if zz_in_Pn 512 537%nat then Z.of_nat 537%nat else 1%Z) * ((if zz_in_Pn 512 538%nat then Z.of_nat 538%nat else 1%Z) * ((if zz_in_Pn 512 539%nat then Z.of_nat 539%nat else 1%Z) * ((if zz_in_Pn 512 540%nat then Z.of_nat 540%nat else 1%Z) * ((if zz_in_Pn 512 541%nat then Z.of_nat 541%nat else 1%Z) * ((if zz_in_Pn 512 542%nat then Z.of_nat 542%nat else 1%Z) * ((if zz_in_Pn 512 543%nat then Z.of_nat 543%nat else 1%Z) * (if zz_in_Pn 512 544%nat then Z.of_nat 544%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_544.
    rewrite piu_zz_inPn_512_543.
    rewrite piu_zz_inPn_512_542.
    rewrite piu_zz_inPn_512_541.
    rewrite piu_zz_inPn_512_540.
    rewrite piu_zz_inPn_512_539.
    rewrite piu_zz_inPn_512_538.
    rewrite piu_zz_inPn_512_537.
    rewrite piu_zz_inPn_512_536.
    rewrite piu_zz_inPn_512_535.
    rewrite piu_zz_inPn_512_534.
    rewrite piu_zz_inPn_512_533.
    rewrite piu_zz_inPn_512_532.
    rewrite piu_zz_inPn_512_531.
    rewrite piu_zz_inPn_512_530.
    rewrite piu_zz_inPn_512_529.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb31 : piu_zz_zprod_seg 512%nat 512%nat 16%nat = ((if zz_in_Pn 512 513%nat then Z.of_nat 513%nat else 1%Z) * ((if zz_in_Pn 512 514%nat then Z.of_nat 514%nat else 1%Z) * ((if zz_in_Pn 512 515%nat then Z.of_nat 515%nat else 1%Z) * ((if zz_in_Pn 512 516%nat then Z.of_nat 516%nat else 1%Z) * ((if zz_in_Pn 512 517%nat then Z.of_nat 517%nat else 1%Z) * ((if zz_in_Pn 512 518%nat then Z.of_nat 518%nat else 1%Z) * ((if zz_in_Pn 512 519%nat then Z.of_nat 519%nat else 1%Z) * ((if zz_in_Pn 512 520%nat then Z.of_nat 520%nat else 1%Z) * ((if zz_in_Pn 512 521%nat then Z.of_nat 521%nat else 1%Z) * ((if zz_in_Pn 512 522%nat then Z.of_nat 522%nat else 1%Z) * ((if zz_in_Pn 512 523%nat then Z.of_nat 523%nat else 1%Z) * ((if zz_in_Pn 512 524%nat then Z.of_nat 524%nat else 1%Z) * ((if zz_in_Pn 512 525%nat then Z.of_nat 525%nat else 1%Z) * ((if zz_in_Pn 512 526%nat then Z.of_nat 526%nat else 1%Z) * ((if zz_in_Pn 512 527%nat then Z.of_nat 527%nat else 1%Z) * (if zz_in_Pn 512 528%nat then Z.of_nat 528%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_528.
    rewrite piu_zz_inPn_512_527.
    rewrite piu_zz_inPn_512_526.
    rewrite piu_zz_inPn_512_525.
    rewrite piu_zz_inPn_512_524.
    rewrite piu_zz_inPn_512_523.
    rewrite piu_zz_inPn_512_522.
    rewrite piu_zz_inPn_512_521.
    rewrite piu_zz_inPn_512_520.
    rewrite piu_zz_inPn_512_519.
    rewrite piu_zz_inPn_512_518.
    rewrite piu_zz_inPn_512_517.
    rewrite piu_zz_inPn_512_516.
    rewrite piu_zz_inPn_512_515.
    rewrite piu_zz_inPn_512_514.
    rewrite piu_zz_inPn_512_513.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  rewrite Hb0.
  rewrite Hb1.
  rewrite Hb2.
  rewrite Hb3.
  rewrite Hb4.
  rewrite Hb5.
  rewrite Hb6.
  rewrite Hb7.
  rewrite Hb8.
  rewrite Hb9.
  rewrite Hb10.
  rewrite Hb11.
  rewrite Hb12.
  rewrite Hb13.
  rewrite Hb14.
  rewrite Hb15.
  rewrite Hb16.
  rewrite Hb17.
  rewrite Hb18.
  rewrite Hb19.
  rewrite Hb20.
  rewrite Hb21.
  rewrite Hb22.
  rewrite Hb23.
  rewrite Hb24.
  rewrite Hb25.
  rewrite Hb26.
  rewrite Hb27.
  rewrite Hb28.
  rewrite Hb29.
  rewrite Hb30.
  rewrite Hb31.
  vm_compute. reflexivity.
Qed.

(* zz_Phi 1024 字面值链。 *)
Definition piu_zz_lit_Phibase_1024 : Z := 2676424583214047812886498025277%Z.
Lemma piu_zz_Phibase_1024 : zz_prodf 1024 512 = piu_zz_lit_Phibase_1024.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_Phi_1024 : Z := 1247265667207878743564411746639630465837680150403967205716038259439454683881228755169778368855472723728093086558056377142445765017511506443750179754482867083617905365271468235023582470869802861523534438052014857889150368227303863291555158486883485396025660116039962900929732129927%Z.
Lemma piu_zz_zzPhi_1024 : zz_Phi 1024 = piu_zz_lit_Phi_1024.
Proof.
  unfold zz_Phi.
  replace (2 * 1024)%nat with (512 + 1536)%nat by lia.
  rewrite (piu_zz_zprod_merge 1024%nat 512%nat 1536%nat).
  rewrite piu_zz_Phibase_1024.
  assert (Hs : forall x a b : nat, piu_zz_zprod_seg 1024%nat x (a + b)%nat = piu_zz_zprod_seg 1024%nat x a * piu_zz_zprod_seg 1024%nat (x + a)%nat b).
  { intros x a b. induction b as [|c IH].
    - cbn [piu_zz_zprod_seg]. rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
    - replace (a + S c)%nat with (S (a + c))%nat by lia.
      cbn [piu_zz_zprod_seg].
      replace (S (x + a + c))%nat with (S (x + (a + c)))%nat by lia.
      rewrite IH. rewrite Z.mul_assoc. reflexivity. }
  change (piu_zz_zprod_seg 1024%nat 512%nat 1536%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1520%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1520%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1520%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1504%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1504%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1504%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1488%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1488%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1488%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1472%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1472%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1472%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1456%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1456%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1456%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1440%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1440%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1440%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1424%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1424%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1424%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1408%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1408%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1408%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1392%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1392%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1392%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1376%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1376%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1376%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1360%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1360%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1360%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1344%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1344%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1344%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1328%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1328%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1328%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1312%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1312%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1312%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1296%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1296%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1296%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1280%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1280%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1280%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1264%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1264%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1264%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1248%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1248%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1248%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1232%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1232%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1232%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1216%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1216%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1216%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1200%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1200%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1200%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1184%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1184%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1184%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1168%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1168%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1168%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1152%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1152%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1152%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1136%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1136%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1136%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1120%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1120%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1120%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1104%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1104%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1104%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1088%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1088%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1088%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1072%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1072%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1072%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1056%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1056%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1056%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1040%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1040%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1040%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1024%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1024%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1024%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (1008%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 1008%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 1008%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (992%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 992%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 992%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (976%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 976%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 976%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (960%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 960%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 960%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (944%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 944%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 944%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (928%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 928%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 928%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (912%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 912%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 912%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (896%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 896%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 896%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (880%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 880%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 880%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (864%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 864%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 864%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (848%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 848%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 848%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (832%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 832%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 832%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (816%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 816%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 816%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (800%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 800%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 800%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (784%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 784%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 784%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (768%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 768%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 768%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (752%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 752%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 752%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (736%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 736%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 736%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (720%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 720%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 720%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (704%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 704%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 704%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (688%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 688%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 688%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (672%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 672%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 672%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (656%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 656%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 656%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (640%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 640%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 640%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (624%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 624%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 624%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (608%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 608%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 608%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (592%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 592%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 592%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (576%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 576%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 576%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (560%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 560%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 560%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (544%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 544%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 544%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (528%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 528%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 528%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (512%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 512%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 512%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (496%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 496%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 496%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (480%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 480%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 480%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (464%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 464%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 464%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (448%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 448%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 448%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (432%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 432%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 432%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (416%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 416%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 416%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (400%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 400%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 400%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (384%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 384%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 384%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (368%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 368%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 368%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (352%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 352%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 352%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (336%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 336%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 336%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (320%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 320%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 320%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (304%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 304%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 304%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (288%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 288%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 288%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (272%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 272%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 272%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (256%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 256%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 256%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (240%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 240%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 240%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (224%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 224%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 224%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (208%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 208%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 208%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (192%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 192%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 192%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (176%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 176%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 176%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (160%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 160%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 160%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (144%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 144%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 144%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (128%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 128%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 128%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (112%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 112%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 112%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (96%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 96%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 96%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (80%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 80%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 80%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (64%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 64%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 64%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (48%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 48%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 48%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (32%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 32%nat 16%nat).
  change (piu_zz_zprod_seg 1024%nat 512%nat 32%nat) with (piu_zz_zprod_seg 1024%nat 512%nat (16%nat + 16%nat)%nat).
  rewrite (Hs 512%nat 16%nat 16%nat).
  assert (Hb0 : piu_zz_zprod_seg 1024%nat (512%nat + 1520%nat) 16%nat = ((if zz_in_Pn 1024 2033%nat then Z.of_nat 2033%nat else 1%Z) * ((if zz_in_Pn 1024 2034%nat then Z.of_nat 2034%nat else 1%Z) * ((if zz_in_Pn 1024 2035%nat then Z.of_nat 2035%nat else 1%Z) * ((if zz_in_Pn 1024 2036%nat then Z.of_nat 2036%nat else 1%Z) * ((if zz_in_Pn 1024 2037%nat then Z.of_nat 2037%nat else 1%Z) * ((if zz_in_Pn 1024 2038%nat then Z.of_nat 2038%nat else 1%Z) * ((if zz_in_Pn 1024 2039%nat then Z.of_nat 2039%nat else 1%Z) * ((if zz_in_Pn 1024 2040%nat then Z.of_nat 2040%nat else 1%Z) * ((if zz_in_Pn 1024 2041%nat then Z.of_nat 2041%nat else 1%Z) * ((if zz_in_Pn 1024 2042%nat then Z.of_nat 2042%nat else 1%Z) * ((if zz_in_Pn 1024 2043%nat then Z.of_nat 2043%nat else 1%Z) * ((if zz_in_Pn 1024 2044%nat then Z.of_nat 2044%nat else 1%Z) * ((if zz_in_Pn 1024 2045%nat then Z.of_nat 2045%nat else 1%Z) * ((if zz_in_Pn 1024 2046%nat then Z.of_nat 2046%nat else 1%Z) * ((if zz_in_Pn 1024 2047%nat then Z.of_nat 2047%nat else 1%Z) * (if zz_in_Pn 1024 2048%nat then Z.of_nat 2048%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2048.
    rewrite piu_zz_inPn_1024_2047.
    rewrite piu_zz_inPn_1024_2046.
    rewrite piu_zz_inPn_1024_2045.
    rewrite piu_zz_inPn_1024_2044.
    rewrite piu_zz_inPn_1024_2043.
    rewrite piu_zz_inPn_1024_2042.
    rewrite piu_zz_inPn_1024_2041.
    rewrite piu_zz_inPn_1024_2040.
    rewrite piu_zz_inPn_1024_2039.
    rewrite piu_zz_inPn_1024_2038.
    rewrite piu_zz_inPn_1024_2037.
    rewrite piu_zz_inPn_1024_2036.
    rewrite piu_zz_inPn_1024_2035.
    rewrite piu_zz_inPn_1024_2034.
    rewrite piu_zz_inPn_1024_2033.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb1 : piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) 16%nat = ((if zz_in_Pn 1024 2017%nat then Z.of_nat 2017%nat else 1%Z) * ((if zz_in_Pn 1024 2018%nat then Z.of_nat 2018%nat else 1%Z) * ((if zz_in_Pn 1024 2019%nat then Z.of_nat 2019%nat else 1%Z) * ((if zz_in_Pn 1024 2020%nat then Z.of_nat 2020%nat else 1%Z) * ((if zz_in_Pn 1024 2021%nat then Z.of_nat 2021%nat else 1%Z) * ((if zz_in_Pn 1024 2022%nat then Z.of_nat 2022%nat else 1%Z) * ((if zz_in_Pn 1024 2023%nat then Z.of_nat 2023%nat else 1%Z) * ((if zz_in_Pn 1024 2024%nat then Z.of_nat 2024%nat else 1%Z) * ((if zz_in_Pn 1024 2025%nat then Z.of_nat 2025%nat else 1%Z) * ((if zz_in_Pn 1024 2026%nat then Z.of_nat 2026%nat else 1%Z) * ((if zz_in_Pn 1024 2027%nat then Z.of_nat 2027%nat else 1%Z) * ((if zz_in_Pn 1024 2028%nat then Z.of_nat 2028%nat else 1%Z) * ((if zz_in_Pn 1024 2029%nat then Z.of_nat 2029%nat else 1%Z) * ((if zz_in_Pn 1024 2030%nat then Z.of_nat 2030%nat else 1%Z) * ((if zz_in_Pn 1024 2031%nat then Z.of_nat 2031%nat else 1%Z) * (if zz_in_Pn 1024 2032%nat then Z.of_nat 2032%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2032.
    rewrite piu_zz_inPn_1024_2031.
    rewrite piu_zz_inPn_1024_2030.
    rewrite piu_zz_inPn_1024_2029.
    rewrite piu_zz_inPn_1024_2028.
    rewrite piu_zz_inPn_1024_2027.
    rewrite piu_zz_inPn_1024_2026.
    rewrite piu_zz_inPn_1024_2025.
    rewrite piu_zz_inPn_1024_2024.
    rewrite piu_zz_inPn_1024_2023.
    rewrite piu_zz_inPn_1024_2022.
    rewrite piu_zz_inPn_1024_2021.
    rewrite piu_zz_inPn_1024_2020.
    rewrite piu_zz_inPn_1024_2019.
    rewrite piu_zz_inPn_1024_2018.
    rewrite piu_zz_inPn_1024_2017.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb2 : piu_zz_zprod_seg 1024%nat (512%nat + 1488%nat) 16%nat = ((if zz_in_Pn 1024 2001%nat then Z.of_nat 2001%nat else 1%Z) * ((if zz_in_Pn 1024 2002%nat then Z.of_nat 2002%nat else 1%Z) * ((if zz_in_Pn 1024 2003%nat then Z.of_nat 2003%nat else 1%Z) * ((if zz_in_Pn 1024 2004%nat then Z.of_nat 2004%nat else 1%Z) * ((if zz_in_Pn 1024 2005%nat then Z.of_nat 2005%nat else 1%Z) * ((if zz_in_Pn 1024 2006%nat then Z.of_nat 2006%nat else 1%Z) * ((if zz_in_Pn 1024 2007%nat then Z.of_nat 2007%nat else 1%Z) * ((if zz_in_Pn 1024 2008%nat then Z.of_nat 2008%nat else 1%Z) * ((if zz_in_Pn 1024 2009%nat then Z.of_nat 2009%nat else 1%Z) * ((if zz_in_Pn 1024 2010%nat then Z.of_nat 2010%nat else 1%Z) * ((if zz_in_Pn 1024 2011%nat then Z.of_nat 2011%nat else 1%Z) * ((if zz_in_Pn 1024 2012%nat then Z.of_nat 2012%nat else 1%Z) * ((if zz_in_Pn 1024 2013%nat then Z.of_nat 2013%nat else 1%Z) * ((if zz_in_Pn 1024 2014%nat then Z.of_nat 2014%nat else 1%Z) * ((if zz_in_Pn 1024 2015%nat then Z.of_nat 2015%nat else 1%Z) * (if zz_in_Pn 1024 2016%nat then Z.of_nat 2016%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2016.
    rewrite piu_zz_inPn_1024_2015.
    rewrite piu_zz_inPn_1024_2014.
    rewrite piu_zz_inPn_1024_2013.
    rewrite piu_zz_inPn_1024_2012.
    rewrite piu_zz_inPn_1024_2011.
    rewrite piu_zz_inPn_1024_2010.
    rewrite piu_zz_inPn_1024_2009.
    rewrite piu_zz_inPn_1024_2008.
    rewrite piu_zz_inPn_1024_2007.
    rewrite piu_zz_inPn_1024_2006.
    rewrite piu_zz_inPn_1024_2005.
    rewrite piu_zz_inPn_1024_2004.
    rewrite piu_zz_inPn_1024_2003.
    rewrite piu_zz_inPn_1024_2002.
    rewrite piu_zz_inPn_1024_2001.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb3 : piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 16%nat = ((if zz_in_Pn 1024 1985%nat then Z.of_nat 1985%nat else 1%Z) * ((if zz_in_Pn 1024 1986%nat then Z.of_nat 1986%nat else 1%Z) * ((if zz_in_Pn 1024 1987%nat then Z.of_nat 1987%nat else 1%Z) * ((if zz_in_Pn 1024 1988%nat then Z.of_nat 1988%nat else 1%Z) * ((if zz_in_Pn 1024 1989%nat then Z.of_nat 1989%nat else 1%Z) * ((if zz_in_Pn 1024 1990%nat then Z.of_nat 1990%nat else 1%Z) * ((if zz_in_Pn 1024 1991%nat then Z.of_nat 1991%nat else 1%Z) * ((if zz_in_Pn 1024 1992%nat then Z.of_nat 1992%nat else 1%Z) * ((if zz_in_Pn 1024 1993%nat then Z.of_nat 1993%nat else 1%Z) * ((if zz_in_Pn 1024 1994%nat then Z.of_nat 1994%nat else 1%Z) * ((if zz_in_Pn 1024 1995%nat then Z.of_nat 1995%nat else 1%Z) * ((if zz_in_Pn 1024 1996%nat then Z.of_nat 1996%nat else 1%Z) * ((if zz_in_Pn 1024 1997%nat then Z.of_nat 1997%nat else 1%Z) * ((if zz_in_Pn 1024 1998%nat then Z.of_nat 1998%nat else 1%Z) * ((if zz_in_Pn 1024 1999%nat then Z.of_nat 1999%nat else 1%Z) * (if zz_in_Pn 1024 2000%nat then Z.of_nat 2000%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_2000.
    rewrite piu_zz_inPn_1024_1999.
    rewrite piu_zz_inPn_1024_1998.
    rewrite piu_zz_inPn_1024_1997.
    rewrite piu_zz_inPn_1024_1996.
    rewrite piu_zz_inPn_1024_1995.
    rewrite piu_zz_inPn_1024_1994.
    rewrite piu_zz_inPn_1024_1993.
    rewrite piu_zz_inPn_1024_1992.
    rewrite piu_zz_inPn_1024_1991.
    rewrite piu_zz_inPn_1024_1990.
    rewrite piu_zz_inPn_1024_1989.
    rewrite piu_zz_inPn_1024_1988.
    rewrite piu_zz_inPn_1024_1987.
    rewrite piu_zz_inPn_1024_1986.
    rewrite piu_zz_inPn_1024_1985.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb4 : piu_zz_zprod_seg 1024%nat (512%nat + 1456%nat) 16%nat = ((if zz_in_Pn 1024 1969%nat then Z.of_nat 1969%nat else 1%Z) * ((if zz_in_Pn 1024 1970%nat then Z.of_nat 1970%nat else 1%Z) * ((if zz_in_Pn 1024 1971%nat then Z.of_nat 1971%nat else 1%Z) * ((if zz_in_Pn 1024 1972%nat then Z.of_nat 1972%nat else 1%Z) * ((if zz_in_Pn 1024 1973%nat then Z.of_nat 1973%nat else 1%Z) * ((if zz_in_Pn 1024 1974%nat then Z.of_nat 1974%nat else 1%Z) * ((if zz_in_Pn 1024 1975%nat then Z.of_nat 1975%nat else 1%Z) * ((if zz_in_Pn 1024 1976%nat then Z.of_nat 1976%nat else 1%Z) * ((if zz_in_Pn 1024 1977%nat then Z.of_nat 1977%nat else 1%Z) * ((if zz_in_Pn 1024 1978%nat then Z.of_nat 1978%nat else 1%Z) * ((if zz_in_Pn 1024 1979%nat then Z.of_nat 1979%nat else 1%Z) * ((if zz_in_Pn 1024 1980%nat then Z.of_nat 1980%nat else 1%Z) * ((if zz_in_Pn 1024 1981%nat then Z.of_nat 1981%nat else 1%Z) * ((if zz_in_Pn 1024 1982%nat then Z.of_nat 1982%nat else 1%Z) * ((if zz_in_Pn 1024 1983%nat then Z.of_nat 1983%nat else 1%Z) * (if zz_in_Pn 1024 1984%nat then Z.of_nat 1984%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1984.
    rewrite piu_zz_inPn_1024_1983.
    rewrite piu_zz_inPn_1024_1982.
    rewrite piu_zz_inPn_1024_1981.
    rewrite piu_zz_inPn_1024_1980.
    rewrite piu_zz_inPn_1024_1979.
    rewrite piu_zz_inPn_1024_1978.
    rewrite piu_zz_inPn_1024_1977.
    rewrite piu_zz_inPn_1024_1976.
    rewrite piu_zz_inPn_1024_1975.
    rewrite piu_zz_inPn_1024_1974.
    rewrite piu_zz_inPn_1024_1973.
    rewrite piu_zz_inPn_1024_1972.
    rewrite piu_zz_inPn_1024_1971.
    rewrite piu_zz_inPn_1024_1970.
    rewrite piu_zz_inPn_1024_1969.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb5 : piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) 16%nat = ((if zz_in_Pn 1024 1953%nat then Z.of_nat 1953%nat else 1%Z) * ((if zz_in_Pn 1024 1954%nat then Z.of_nat 1954%nat else 1%Z) * ((if zz_in_Pn 1024 1955%nat then Z.of_nat 1955%nat else 1%Z) * ((if zz_in_Pn 1024 1956%nat then Z.of_nat 1956%nat else 1%Z) * ((if zz_in_Pn 1024 1957%nat then Z.of_nat 1957%nat else 1%Z) * ((if zz_in_Pn 1024 1958%nat then Z.of_nat 1958%nat else 1%Z) * ((if zz_in_Pn 1024 1959%nat then Z.of_nat 1959%nat else 1%Z) * ((if zz_in_Pn 1024 1960%nat then Z.of_nat 1960%nat else 1%Z) * ((if zz_in_Pn 1024 1961%nat then Z.of_nat 1961%nat else 1%Z) * ((if zz_in_Pn 1024 1962%nat then Z.of_nat 1962%nat else 1%Z) * ((if zz_in_Pn 1024 1963%nat then Z.of_nat 1963%nat else 1%Z) * ((if zz_in_Pn 1024 1964%nat then Z.of_nat 1964%nat else 1%Z) * ((if zz_in_Pn 1024 1965%nat then Z.of_nat 1965%nat else 1%Z) * ((if zz_in_Pn 1024 1966%nat then Z.of_nat 1966%nat else 1%Z) * ((if zz_in_Pn 1024 1967%nat then Z.of_nat 1967%nat else 1%Z) * (if zz_in_Pn 1024 1968%nat then Z.of_nat 1968%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1968.
    rewrite piu_zz_inPn_1024_1967.
    rewrite piu_zz_inPn_1024_1966.
    rewrite piu_zz_inPn_1024_1965.
    rewrite piu_zz_inPn_1024_1964.
    rewrite piu_zz_inPn_1024_1963.
    rewrite piu_zz_inPn_1024_1962.
    rewrite piu_zz_inPn_1024_1961.
    rewrite piu_zz_inPn_1024_1960.
    rewrite piu_zz_inPn_1024_1959.
    rewrite piu_zz_inPn_1024_1958.
    rewrite piu_zz_inPn_1024_1957.
    rewrite piu_zz_inPn_1024_1956.
    rewrite piu_zz_inPn_1024_1955.
    rewrite piu_zz_inPn_1024_1954.
    rewrite piu_zz_inPn_1024_1953.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb6 : piu_zz_zprod_seg 1024%nat (512%nat + 1424%nat) 16%nat = ((if zz_in_Pn 1024 1937%nat then Z.of_nat 1937%nat else 1%Z) * ((if zz_in_Pn 1024 1938%nat then Z.of_nat 1938%nat else 1%Z) * ((if zz_in_Pn 1024 1939%nat then Z.of_nat 1939%nat else 1%Z) * ((if zz_in_Pn 1024 1940%nat then Z.of_nat 1940%nat else 1%Z) * ((if zz_in_Pn 1024 1941%nat then Z.of_nat 1941%nat else 1%Z) * ((if zz_in_Pn 1024 1942%nat then Z.of_nat 1942%nat else 1%Z) * ((if zz_in_Pn 1024 1943%nat then Z.of_nat 1943%nat else 1%Z) * ((if zz_in_Pn 1024 1944%nat then Z.of_nat 1944%nat else 1%Z) * ((if zz_in_Pn 1024 1945%nat then Z.of_nat 1945%nat else 1%Z) * ((if zz_in_Pn 1024 1946%nat then Z.of_nat 1946%nat else 1%Z) * ((if zz_in_Pn 1024 1947%nat then Z.of_nat 1947%nat else 1%Z) * ((if zz_in_Pn 1024 1948%nat then Z.of_nat 1948%nat else 1%Z) * ((if zz_in_Pn 1024 1949%nat then Z.of_nat 1949%nat else 1%Z) * ((if zz_in_Pn 1024 1950%nat then Z.of_nat 1950%nat else 1%Z) * ((if zz_in_Pn 1024 1951%nat then Z.of_nat 1951%nat else 1%Z) * (if zz_in_Pn 1024 1952%nat then Z.of_nat 1952%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1952.
    rewrite piu_zz_inPn_1024_1951.
    rewrite piu_zz_inPn_1024_1950.
    rewrite piu_zz_inPn_1024_1949.
    rewrite piu_zz_inPn_1024_1948.
    rewrite piu_zz_inPn_1024_1947.
    rewrite piu_zz_inPn_1024_1946.
    rewrite piu_zz_inPn_1024_1945.
    rewrite piu_zz_inPn_1024_1944.
    rewrite piu_zz_inPn_1024_1943.
    rewrite piu_zz_inPn_1024_1942.
    rewrite piu_zz_inPn_1024_1941.
    rewrite piu_zz_inPn_1024_1940.
    rewrite piu_zz_inPn_1024_1939.
    rewrite piu_zz_inPn_1024_1938.
    rewrite piu_zz_inPn_1024_1937.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb7 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 16%nat = ((if zz_in_Pn 1024 1921%nat then Z.of_nat 1921%nat else 1%Z) * ((if zz_in_Pn 1024 1922%nat then Z.of_nat 1922%nat else 1%Z) * ((if zz_in_Pn 1024 1923%nat then Z.of_nat 1923%nat else 1%Z) * ((if zz_in_Pn 1024 1924%nat then Z.of_nat 1924%nat else 1%Z) * ((if zz_in_Pn 1024 1925%nat then Z.of_nat 1925%nat else 1%Z) * ((if zz_in_Pn 1024 1926%nat then Z.of_nat 1926%nat else 1%Z) * ((if zz_in_Pn 1024 1927%nat then Z.of_nat 1927%nat else 1%Z) * ((if zz_in_Pn 1024 1928%nat then Z.of_nat 1928%nat else 1%Z) * ((if zz_in_Pn 1024 1929%nat then Z.of_nat 1929%nat else 1%Z) * ((if zz_in_Pn 1024 1930%nat then Z.of_nat 1930%nat else 1%Z) * ((if zz_in_Pn 1024 1931%nat then Z.of_nat 1931%nat else 1%Z) * ((if zz_in_Pn 1024 1932%nat then Z.of_nat 1932%nat else 1%Z) * ((if zz_in_Pn 1024 1933%nat then Z.of_nat 1933%nat else 1%Z) * ((if zz_in_Pn 1024 1934%nat then Z.of_nat 1934%nat else 1%Z) * ((if zz_in_Pn 1024 1935%nat then Z.of_nat 1935%nat else 1%Z) * (if zz_in_Pn 1024 1936%nat then Z.of_nat 1936%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1936.
    rewrite piu_zz_inPn_1024_1935.
    rewrite piu_zz_inPn_1024_1934.
    rewrite piu_zz_inPn_1024_1933.
    rewrite piu_zz_inPn_1024_1932.
    rewrite piu_zz_inPn_1024_1931.
    rewrite piu_zz_inPn_1024_1930.
    rewrite piu_zz_inPn_1024_1929.
    rewrite piu_zz_inPn_1024_1928.
    rewrite piu_zz_inPn_1024_1927.
    rewrite piu_zz_inPn_1024_1926.
    rewrite piu_zz_inPn_1024_1925.
    rewrite piu_zz_inPn_1024_1924.
    rewrite piu_zz_inPn_1024_1923.
    rewrite piu_zz_inPn_1024_1922.
    rewrite piu_zz_inPn_1024_1921.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb8 : piu_zz_zprod_seg 1024%nat (512%nat + 1392%nat) 16%nat = ((if zz_in_Pn 1024 1905%nat then Z.of_nat 1905%nat else 1%Z) * ((if zz_in_Pn 1024 1906%nat then Z.of_nat 1906%nat else 1%Z) * ((if zz_in_Pn 1024 1907%nat then Z.of_nat 1907%nat else 1%Z) * ((if zz_in_Pn 1024 1908%nat then Z.of_nat 1908%nat else 1%Z) * ((if zz_in_Pn 1024 1909%nat then Z.of_nat 1909%nat else 1%Z) * ((if zz_in_Pn 1024 1910%nat then Z.of_nat 1910%nat else 1%Z) * ((if zz_in_Pn 1024 1911%nat then Z.of_nat 1911%nat else 1%Z) * ((if zz_in_Pn 1024 1912%nat then Z.of_nat 1912%nat else 1%Z) * ((if zz_in_Pn 1024 1913%nat then Z.of_nat 1913%nat else 1%Z) * ((if zz_in_Pn 1024 1914%nat then Z.of_nat 1914%nat else 1%Z) * ((if zz_in_Pn 1024 1915%nat then Z.of_nat 1915%nat else 1%Z) * ((if zz_in_Pn 1024 1916%nat then Z.of_nat 1916%nat else 1%Z) * ((if zz_in_Pn 1024 1917%nat then Z.of_nat 1917%nat else 1%Z) * ((if zz_in_Pn 1024 1918%nat then Z.of_nat 1918%nat else 1%Z) * ((if zz_in_Pn 1024 1919%nat then Z.of_nat 1919%nat else 1%Z) * (if zz_in_Pn 1024 1920%nat then Z.of_nat 1920%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1920.
    rewrite piu_zz_inPn_1024_1919.
    rewrite piu_zz_inPn_1024_1918.
    rewrite piu_zz_inPn_1024_1917.
    rewrite piu_zz_inPn_1024_1916.
    rewrite piu_zz_inPn_1024_1915.
    rewrite piu_zz_inPn_1024_1914.
    rewrite piu_zz_inPn_1024_1913.
    rewrite piu_zz_inPn_1024_1912.
    rewrite piu_zz_inPn_1024_1911.
    rewrite piu_zz_inPn_1024_1910.
    rewrite piu_zz_inPn_1024_1909.
    rewrite piu_zz_inPn_1024_1908.
    rewrite piu_zz_inPn_1024_1907.
    rewrite piu_zz_inPn_1024_1906.
    rewrite piu_zz_inPn_1024_1905.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb9 : piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) 16%nat = ((if zz_in_Pn 1024 1889%nat then Z.of_nat 1889%nat else 1%Z) * ((if zz_in_Pn 1024 1890%nat then Z.of_nat 1890%nat else 1%Z) * ((if zz_in_Pn 1024 1891%nat then Z.of_nat 1891%nat else 1%Z) * ((if zz_in_Pn 1024 1892%nat then Z.of_nat 1892%nat else 1%Z) * ((if zz_in_Pn 1024 1893%nat then Z.of_nat 1893%nat else 1%Z) * ((if zz_in_Pn 1024 1894%nat then Z.of_nat 1894%nat else 1%Z) * ((if zz_in_Pn 1024 1895%nat then Z.of_nat 1895%nat else 1%Z) * ((if zz_in_Pn 1024 1896%nat then Z.of_nat 1896%nat else 1%Z) * ((if zz_in_Pn 1024 1897%nat then Z.of_nat 1897%nat else 1%Z) * ((if zz_in_Pn 1024 1898%nat then Z.of_nat 1898%nat else 1%Z) * ((if zz_in_Pn 1024 1899%nat then Z.of_nat 1899%nat else 1%Z) * ((if zz_in_Pn 1024 1900%nat then Z.of_nat 1900%nat else 1%Z) * ((if zz_in_Pn 1024 1901%nat then Z.of_nat 1901%nat else 1%Z) * ((if zz_in_Pn 1024 1902%nat then Z.of_nat 1902%nat else 1%Z) * ((if zz_in_Pn 1024 1903%nat then Z.of_nat 1903%nat else 1%Z) * (if zz_in_Pn 1024 1904%nat then Z.of_nat 1904%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1904.
    rewrite piu_zz_inPn_1024_1903.
    rewrite piu_zz_inPn_1024_1902.
    rewrite piu_zz_inPn_1024_1901.
    rewrite piu_zz_inPn_1024_1900.
    rewrite piu_zz_inPn_1024_1899.
    rewrite piu_zz_inPn_1024_1898.
    rewrite piu_zz_inPn_1024_1897.
    rewrite piu_zz_inPn_1024_1896.
    rewrite piu_zz_inPn_1024_1895.
    rewrite piu_zz_inPn_1024_1894.
    rewrite piu_zz_inPn_1024_1893.
    rewrite piu_zz_inPn_1024_1892.
    rewrite piu_zz_inPn_1024_1891.
    rewrite piu_zz_inPn_1024_1890.
    rewrite piu_zz_inPn_1024_1889.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb10 : piu_zz_zprod_seg 1024%nat (512%nat + 1360%nat) 16%nat = ((if zz_in_Pn 1024 1873%nat then Z.of_nat 1873%nat else 1%Z) * ((if zz_in_Pn 1024 1874%nat then Z.of_nat 1874%nat else 1%Z) * ((if zz_in_Pn 1024 1875%nat then Z.of_nat 1875%nat else 1%Z) * ((if zz_in_Pn 1024 1876%nat then Z.of_nat 1876%nat else 1%Z) * ((if zz_in_Pn 1024 1877%nat then Z.of_nat 1877%nat else 1%Z) * ((if zz_in_Pn 1024 1878%nat then Z.of_nat 1878%nat else 1%Z) * ((if zz_in_Pn 1024 1879%nat then Z.of_nat 1879%nat else 1%Z) * ((if zz_in_Pn 1024 1880%nat then Z.of_nat 1880%nat else 1%Z) * ((if zz_in_Pn 1024 1881%nat then Z.of_nat 1881%nat else 1%Z) * ((if zz_in_Pn 1024 1882%nat then Z.of_nat 1882%nat else 1%Z) * ((if zz_in_Pn 1024 1883%nat then Z.of_nat 1883%nat else 1%Z) * ((if zz_in_Pn 1024 1884%nat then Z.of_nat 1884%nat else 1%Z) * ((if zz_in_Pn 1024 1885%nat then Z.of_nat 1885%nat else 1%Z) * ((if zz_in_Pn 1024 1886%nat then Z.of_nat 1886%nat else 1%Z) * ((if zz_in_Pn 1024 1887%nat then Z.of_nat 1887%nat else 1%Z) * (if zz_in_Pn 1024 1888%nat then Z.of_nat 1888%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1888.
    rewrite piu_zz_inPn_1024_1887.
    rewrite piu_zz_inPn_1024_1886.
    rewrite piu_zz_inPn_1024_1885.
    rewrite piu_zz_inPn_1024_1884.
    rewrite piu_zz_inPn_1024_1883.
    rewrite piu_zz_inPn_1024_1882.
    rewrite piu_zz_inPn_1024_1881.
    rewrite piu_zz_inPn_1024_1880.
    rewrite piu_zz_inPn_1024_1879.
    rewrite piu_zz_inPn_1024_1878.
    rewrite piu_zz_inPn_1024_1877.
    rewrite piu_zz_inPn_1024_1876.
    rewrite piu_zz_inPn_1024_1875.
    rewrite piu_zz_inPn_1024_1874.
    rewrite piu_zz_inPn_1024_1873.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb11 : piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 16%nat = ((if zz_in_Pn 1024 1857%nat then Z.of_nat 1857%nat else 1%Z) * ((if zz_in_Pn 1024 1858%nat then Z.of_nat 1858%nat else 1%Z) * ((if zz_in_Pn 1024 1859%nat then Z.of_nat 1859%nat else 1%Z) * ((if zz_in_Pn 1024 1860%nat then Z.of_nat 1860%nat else 1%Z) * ((if zz_in_Pn 1024 1861%nat then Z.of_nat 1861%nat else 1%Z) * ((if zz_in_Pn 1024 1862%nat then Z.of_nat 1862%nat else 1%Z) * ((if zz_in_Pn 1024 1863%nat then Z.of_nat 1863%nat else 1%Z) * ((if zz_in_Pn 1024 1864%nat then Z.of_nat 1864%nat else 1%Z) * ((if zz_in_Pn 1024 1865%nat then Z.of_nat 1865%nat else 1%Z) * ((if zz_in_Pn 1024 1866%nat then Z.of_nat 1866%nat else 1%Z) * ((if zz_in_Pn 1024 1867%nat then Z.of_nat 1867%nat else 1%Z) * ((if zz_in_Pn 1024 1868%nat then Z.of_nat 1868%nat else 1%Z) * ((if zz_in_Pn 1024 1869%nat then Z.of_nat 1869%nat else 1%Z) * ((if zz_in_Pn 1024 1870%nat then Z.of_nat 1870%nat else 1%Z) * ((if zz_in_Pn 1024 1871%nat then Z.of_nat 1871%nat else 1%Z) * (if zz_in_Pn 1024 1872%nat then Z.of_nat 1872%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1872.
    rewrite piu_zz_inPn_1024_1871.
    rewrite piu_zz_inPn_1024_1870.
    rewrite piu_zz_inPn_1024_1869.
    rewrite piu_zz_inPn_1024_1868.
    rewrite piu_zz_inPn_1024_1867.
    rewrite piu_zz_inPn_1024_1866.
    rewrite piu_zz_inPn_1024_1865.
    rewrite piu_zz_inPn_1024_1864.
    rewrite piu_zz_inPn_1024_1863.
    rewrite piu_zz_inPn_1024_1862.
    rewrite piu_zz_inPn_1024_1861.
    rewrite piu_zz_inPn_1024_1860.
    rewrite piu_zz_inPn_1024_1859.
    rewrite piu_zz_inPn_1024_1858.
    rewrite piu_zz_inPn_1024_1857.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb12 : piu_zz_zprod_seg 1024%nat (512%nat + 1328%nat) 16%nat = ((if zz_in_Pn 1024 1841%nat then Z.of_nat 1841%nat else 1%Z) * ((if zz_in_Pn 1024 1842%nat then Z.of_nat 1842%nat else 1%Z) * ((if zz_in_Pn 1024 1843%nat then Z.of_nat 1843%nat else 1%Z) * ((if zz_in_Pn 1024 1844%nat then Z.of_nat 1844%nat else 1%Z) * ((if zz_in_Pn 1024 1845%nat then Z.of_nat 1845%nat else 1%Z) * ((if zz_in_Pn 1024 1846%nat then Z.of_nat 1846%nat else 1%Z) * ((if zz_in_Pn 1024 1847%nat then Z.of_nat 1847%nat else 1%Z) * ((if zz_in_Pn 1024 1848%nat then Z.of_nat 1848%nat else 1%Z) * ((if zz_in_Pn 1024 1849%nat then Z.of_nat 1849%nat else 1%Z) * ((if zz_in_Pn 1024 1850%nat then Z.of_nat 1850%nat else 1%Z) * ((if zz_in_Pn 1024 1851%nat then Z.of_nat 1851%nat else 1%Z) * ((if zz_in_Pn 1024 1852%nat then Z.of_nat 1852%nat else 1%Z) * ((if zz_in_Pn 1024 1853%nat then Z.of_nat 1853%nat else 1%Z) * ((if zz_in_Pn 1024 1854%nat then Z.of_nat 1854%nat else 1%Z) * ((if zz_in_Pn 1024 1855%nat then Z.of_nat 1855%nat else 1%Z) * (if zz_in_Pn 1024 1856%nat then Z.of_nat 1856%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1856.
    rewrite piu_zz_inPn_1024_1855.
    rewrite piu_zz_inPn_1024_1854.
    rewrite piu_zz_inPn_1024_1853.
    rewrite piu_zz_inPn_1024_1852.
    rewrite piu_zz_inPn_1024_1851.
    rewrite piu_zz_inPn_1024_1850.
    rewrite piu_zz_inPn_1024_1849.
    rewrite piu_zz_inPn_1024_1848.
    rewrite piu_zz_inPn_1024_1847.
    rewrite piu_zz_inPn_1024_1846.
    rewrite piu_zz_inPn_1024_1845.
    rewrite piu_zz_inPn_1024_1844.
    rewrite piu_zz_inPn_1024_1843.
    rewrite piu_zz_inPn_1024_1842.
    rewrite piu_zz_inPn_1024_1841.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb13 : piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) 16%nat = ((if zz_in_Pn 1024 1825%nat then Z.of_nat 1825%nat else 1%Z) * ((if zz_in_Pn 1024 1826%nat then Z.of_nat 1826%nat else 1%Z) * ((if zz_in_Pn 1024 1827%nat then Z.of_nat 1827%nat else 1%Z) * ((if zz_in_Pn 1024 1828%nat then Z.of_nat 1828%nat else 1%Z) * ((if zz_in_Pn 1024 1829%nat then Z.of_nat 1829%nat else 1%Z) * ((if zz_in_Pn 1024 1830%nat then Z.of_nat 1830%nat else 1%Z) * ((if zz_in_Pn 1024 1831%nat then Z.of_nat 1831%nat else 1%Z) * ((if zz_in_Pn 1024 1832%nat then Z.of_nat 1832%nat else 1%Z) * ((if zz_in_Pn 1024 1833%nat then Z.of_nat 1833%nat else 1%Z) * ((if zz_in_Pn 1024 1834%nat then Z.of_nat 1834%nat else 1%Z) * ((if zz_in_Pn 1024 1835%nat then Z.of_nat 1835%nat else 1%Z) * ((if zz_in_Pn 1024 1836%nat then Z.of_nat 1836%nat else 1%Z) * ((if zz_in_Pn 1024 1837%nat then Z.of_nat 1837%nat else 1%Z) * ((if zz_in_Pn 1024 1838%nat then Z.of_nat 1838%nat else 1%Z) * ((if zz_in_Pn 1024 1839%nat then Z.of_nat 1839%nat else 1%Z) * (if zz_in_Pn 1024 1840%nat then Z.of_nat 1840%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1840.
    rewrite piu_zz_inPn_1024_1839.
    rewrite piu_zz_inPn_1024_1838.
    rewrite piu_zz_inPn_1024_1837.
    rewrite piu_zz_inPn_1024_1836.
    rewrite piu_zz_inPn_1024_1835.
    rewrite piu_zz_inPn_1024_1834.
    rewrite piu_zz_inPn_1024_1833.
    rewrite piu_zz_inPn_1024_1832.
    rewrite piu_zz_inPn_1024_1831.
    rewrite piu_zz_inPn_1024_1830.
    rewrite piu_zz_inPn_1024_1829.
    rewrite piu_zz_inPn_1024_1828.
    rewrite piu_zz_inPn_1024_1827.
    rewrite piu_zz_inPn_1024_1826.
    rewrite piu_zz_inPn_1024_1825.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb14 : piu_zz_zprod_seg 1024%nat (512%nat + 1296%nat) 16%nat = ((if zz_in_Pn 1024 1809%nat then Z.of_nat 1809%nat else 1%Z) * ((if zz_in_Pn 1024 1810%nat then Z.of_nat 1810%nat else 1%Z) * ((if zz_in_Pn 1024 1811%nat then Z.of_nat 1811%nat else 1%Z) * ((if zz_in_Pn 1024 1812%nat then Z.of_nat 1812%nat else 1%Z) * ((if zz_in_Pn 1024 1813%nat then Z.of_nat 1813%nat else 1%Z) * ((if zz_in_Pn 1024 1814%nat then Z.of_nat 1814%nat else 1%Z) * ((if zz_in_Pn 1024 1815%nat then Z.of_nat 1815%nat else 1%Z) * ((if zz_in_Pn 1024 1816%nat then Z.of_nat 1816%nat else 1%Z) * ((if zz_in_Pn 1024 1817%nat then Z.of_nat 1817%nat else 1%Z) * ((if zz_in_Pn 1024 1818%nat then Z.of_nat 1818%nat else 1%Z) * ((if zz_in_Pn 1024 1819%nat then Z.of_nat 1819%nat else 1%Z) * ((if zz_in_Pn 1024 1820%nat then Z.of_nat 1820%nat else 1%Z) * ((if zz_in_Pn 1024 1821%nat then Z.of_nat 1821%nat else 1%Z) * ((if zz_in_Pn 1024 1822%nat then Z.of_nat 1822%nat else 1%Z) * ((if zz_in_Pn 1024 1823%nat then Z.of_nat 1823%nat else 1%Z) * (if zz_in_Pn 1024 1824%nat then Z.of_nat 1824%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1824.
    rewrite piu_zz_inPn_1024_1823.
    rewrite piu_zz_inPn_1024_1822.
    rewrite piu_zz_inPn_1024_1821.
    rewrite piu_zz_inPn_1024_1820.
    rewrite piu_zz_inPn_1024_1819.
    rewrite piu_zz_inPn_1024_1818.
    rewrite piu_zz_inPn_1024_1817.
    rewrite piu_zz_inPn_1024_1816.
    rewrite piu_zz_inPn_1024_1815.
    rewrite piu_zz_inPn_1024_1814.
    rewrite piu_zz_inPn_1024_1813.
    rewrite piu_zz_inPn_1024_1812.
    rewrite piu_zz_inPn_1024_1811.
    rewrite piu_zz_inPn_1024_1810.
    rewrite piu_zz_inPn_1024_1809.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb15 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 16%nat = ((if zz_in_Pn 1024 1793%nat then Z.of_nat 1793%nat else 1%Z) * ((if zz_in_Pn 1024 1794%nat then Z.of_nat 1794%nat else 1%Z) * ((if zz_in_Pn 1024 1795%nat then Z.of_nat 1795%nat else 1%Z) * ((if zz_in_Pn 1024 1796%nat then Z.of_nat 1796%nat else 1%Z) * ((if zz_in_Pn 1024 1797%nat then Z.of_nat 1797%nat else 1%Z) * ((if zz_in_Pn 1024 1798%nat then Z.of_nat 1798%nat else 1%Z) * ((if zz_in_Pn 1024 1799%nat then Z.of_nat 1799%nat else 1%Z) * ((if zz_in_Pn 1024 1800%nat then Z.of_nat 1800%nat else 1%Z) * ((if zz_in_Pn 1024 1801%nat then Z.of_nat 1801%nat else 1%Z) * ((if zz_in_Pn 1024 1802%nat then Z.of_nat 1802%nat else 1%Z) * ((if zz_in_Pn 1024 1803%nat then Z.of_nat 1803%nat else 1%Z) * ((if zz_in_Pn 1024 1804%nat then Z.of_nat 1804%nat else 1%Z) * ((if zz_in_Pn 1024 1805%nat then Z.of_nat 1805%nat else 1%Z) * ((if zz_in_Pn 1024 1806%nat then Z.of_nat 1806%nat else 1%Z) * ((if zz_in_Pn 1024 1807%nat then Z.of_nat 1807%nat else 1%Z) * (if zz_in_Pn 1024 1808%nat then Z.of_nat 1808%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1808.
    rewrite piu_zz_inPn_1024_1807.
    rewrite piu_zz_inPn_1024_1806.
    rewrite piu_zz_inPn_1024_1805.
    rewrite piu_zz_inPn_1024_1804.
    rewrite piu_zz_inPn_1024_1803.
    rewrite piu_zz_inPn_1024_1802.
    rewrite piu_zz_inPn_1024_1801.
    rewrite piu_zz_inPn_1024_1800.
    rewrite piu_zz_inPn_1024_1799.
    rewrite piu_zz_inPn_1024_1798.
    rewrite piu_zz_inPn_1024_1797.
    rewrite piu_zz_inPn_1024_1796.
    rewrite piu_zz_inPn_1024_1795.
    rewrite piu_zz_inPn_1024_1794.
    rewrite piu_zz_inPn_1024_1793.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb16 : piu_zz_zprod_seg 1024%nat (512%nat + 1264%nat) 16%nat = ((if zz_in_Pn 1024 1777%nat then Z.of_nat 1777%nat else 1%Z) * ((if zz_in_Pn 1024 1778%nat then Z.of_nat 1778%nat else 1%Z) * ((if zz_in_Pn 1024 1779%nat then Z.of_nat 1779%nat else 1%Z) * ((if zz_in_Pn 1024 1780%nat then Z.of_nat 1780%nat else 1%Z) * ((if zz_in_Pn 1024 1781%nat then Z.of_nat 1781%nat else 1%Z) * ((if zz_in_Pn 1024 1782%nat then Z.of_nat 1782%nat else 1%Z) * ((if zz_in_Pn 1024 1783%nat then Z.of_nat 1783%nat else 1%Z) * ((if zz_in_Pn 1024 1784%nat then Z.of_nat 1784%nat else 1%Z) * ((if zz_in_Pn 1024 1785%nat then Z.of_nat 1785%nat else 1%Z) * ((if zz_in_Pn 1024 1786%nat then Z.of_nat 1786%nat else 1%Z) * ((if zz_in_Pn 1024 1787%nat then Z.of_nat 1787%nat else 1%Z) * ((if zz_in_Pn 1024 1788%nat then Z.of_nat 1788%nat else 1%Z) * ((if zz_in_Pn 1024 1789%nat then Z.of_nat 1789%nat else 1%Z) * ((if zz_in_Pn 1024 1790%nat then Z.of_nat 1790%nat else 1%Z) * ((if zz_in_Pn 1024 1791%nat then Z.of_nat 1791%nat else 1%Z) * (if zz_in_Pn 1024 1792%nat then Z.of_nat 1792%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1792.
    rewrite piu_zz_inPn_1024_1791.
    rewrite piu_zz_inPn_1024_1790.
    rewrite piu_zz_inPn_1024_1789.
    rewrite piu_zz_inPn_1024_1788.
    rewrite piu_zz_inPn_1024_1787.
    rewrite piu_zz_inPn_1024_1786.
    rewrite piu_zz_inPn_1024_1785.
    rewrite piu_zz_inPn_1024_1784.
    rewrite piu_zz_inPn_1024_1783.
    rewrite piu_zz_inPn_1024_1782.
    rewrite piu_zz_inPn_1024_1781.
    rewrite piu_zz_inPn_1024_1780.
    rewrite piu_zz_inPn_1024_1779.
    rewrite piu_zz_inPn_1024_1778.
    rewrite piu_zz_inPn_1024_1777.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb17 : piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) 16%nat = ((if zz_in_Pn 1024 1761%nat then Z.of_nat 1761%nat else 1%Z) * ((if zz_in_Pn 1024 1762%nat then Z.of_nat 1762%nat else 1%Z) * ((if zz_in_Pn 1024 1763%nat then Z.of_nat 1763%nat else 1%Z) * ((if zz_in_Pn 1024 1764%nat then Z.of_nat 1764%nat else 1%Z) * ((if zz_in_Pn 1024 1765%nat then Z.of_nat 1765%nat else 1%Z) * ((if zz_in_Pn 1024 1766%nat then Z.of_nat 1766%nat else 1%Z) * ((if zz_in_Pn 1024 1767%nat then Z.of_nat 1767%nat else 1%Z) * ((if zz_in_Pn 1024 1768%nat then Z.of_nat 1768%nat else 1%Z) * ((if zz_in_Pn 1024 1769%nat then Z.of_nat 1769%nat else 1%Z) * ((if zz_in_Pn 1024 1770%nat then Z.of_nat 1770%nat else 1%Z) * ((if zz_in_Pn 1024 1771%nat then Z.of_nat 1771%nat else 1%Z) * ((if zz_in_Pn 1024 1772%nat then Z.of_nat 1772%nat else 1%Z) * ((if zz_in_Pn 1024 1773%nat then Z.of_nat 1773%nat else 1%Z) * ((if zz_in_Pn 1024 1774%nat then Z.of_nat 1774%nat else 1%Z) * ((if zz_in_Pn 1024 1775%nat then Z.of_nat 1775%nat else 1%Z) * (if zz_in_Pn 1024 1776%nat then Z.of_nat 1776%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1776.
    rewrite piu_zz_inPn_1024_1775.
    rewrite piu_zz_inPn_1024_1774.
    rewrite piu_zz_inPn_1024_1773.
    rewrite piu_zz_inPn_1024_1772.
    rewrite piu_zz_inPn_1024_1771.
    rewrite piu_zz_inPn_1024_1770.
    rewrite piu_zz_inPn_1024_1769.
    rewrite piu_zz_inPn_1024_1768.
    rewrite piu_zz_inPn_1024_1767.
    rewrite piu_zz_inPn_1024_1766.
    rewrite piu_zz_inPn_1024_1765.
    rewrite piu_zz_inPn_1024_1764.
    rewrite piu_zz_inPn_1024_1763.
    rewrite piu_zz_inPn_1024_1762.
    rewrite piu_zz_inPn_1024_1761.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb18 : piu_zz_zprod_seg 1024%nat (512%nat + 1232%nat) 16%nat = ((if zz_in_Pn 1024 1745%nat then Z.of_nat 1745%nat else 1%Z) * ((if zz_in_Pn 1024 1746%nat then Z.of_nat 1746%nat else 1%Z) * ((if zz_in_Pn 1024 1747%nat then Z.of_nat 1747%nat else 1%Z) * ((if zz_in_Pn 1024 1748%nat then Z.of_nat 1748%nat else 1%Z) * ((if zz_in_Pn 1024 1749%nat then Z.of_nat 1749%nat else 1%Z) * ((if zz_in_Pn 1024 1750%nat then Z.of_nat 1750%nat else 1%Z) * ((if zz_in_Pn 1024 1751%nat then Z.of_nat 1751%nat else 1%Z) * ((if zz_in_Pn 1024 1752%nat then Z.of_nat 1752%nat else 1%Z) * ((if zz_in_Pn 1024 1753%nat then Z.of_nat 1753%nat else 1%Z) * ((if zz_in_Pn 1024 1754%nat then Z.of_nat 1754%nat else 1%Z) * ((if zz_in_Pn 1024 1755%nat then Z.of_nat 1755%nat else 1%Z) * ((if zz_in_Pn 1024 1756%nat then Z.of_nat 1756%nat else 1%Z) * ((if zz_in_Pn 1024 1757%nat then Z.of_nat 1757%nat else 1%Z) * ((if zz_in_Pn 1024 1758%nat then Z.of_nat 1758%nat else 1%Z) * ((if zz_in_Pn 1024 1759%nat then Z.of_nat 1759%nat else 1%Z) * (if zz_in_Pn 1024 1760%nat then Z.of_nat 1760%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1760.
    rewrite piu_zz_inPn_1024_1759.
    rewrite piu_zz_inPn_1024_1758.
    rewrite piu_zz_inPn_1024_1757.
    rewrite piu_zz_inPn_1024_1756.
    rewrite piu_zz_inPn_1024_1755.
    rewrite piu_zz_inPn_1024_1754.
    rewrite piu_zz_inPn_1024_1753.
    rewrite piu_zz_inPn_1024_1752.
    rewrite piu_zz_inPn_1024_1751.
    rewrite piu_zz_inPn_1024_1750.
    rewrite piu_zz_inPn_1024_1749.
    rewrite piu_zz_inPn_1024_1748.
    rewrite piu_zz_inPn_1024_1747.
    rewrite piu_zz_inPn_1024_1746.
    rewrite piu_zz_inPn_1024_1745.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb19 : piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 16%nat = ((if zz_in_Pn 1024 1729%nat then Z.of_nat 1729%nat else 1%Z) * ((if zz_in_Pn 1024 1730%nat then Z.of_nat 1730%nat else 1%Z) * ((if zz_in_Pn 1024 1731%nat then Z.of_nat 1731%nat else 1%Z) * ((if zz_in_Pn 1024 1732%nat then Z.of_nat 1732%nat else 1%Z) * ((if zz_in_Pn 1024 1733%nat then Z.of_nat 1733%nat else 1%Z) * ((if zz_in_Pn 1024 1734%nat then Z.of_nat 1734%nat else 1%Z) * ((if zz_in_Pn 1024 1735%nat then Z.of_nat 1735%nat else 1%Z) * ((if zz_in_Pn 1024 1736%nat then Z.of_nat 1736%nat else 1%Z) * ((if zz_in_Pn 1024 1737%nat then Z.of_nat 1737%nat else 1%Z) * ((if zz_in_Pn 1024 1738%nat then Z.of_nat 1738%nat else 1%Z) * ((if zz_in_Pn 1024 1739%nat then Z.of_nat 1739%nat else 1%Z) * ((if zz_in_Pn 1024 1740%nat then Z.of_nat 1740%nat else 1%Z) * ((if zz_in_Pn 1024 1741%nat then Z.of_nat 1741%nat else 1%Z) * ((if zz_in_Pn 1024 1742%nat then Z.of_nat 1742%nat else 1%Z) * ((if zz_in_Pn 1024 1743%nat then Z.of_nat 1743%nat else 1%Z) * (if zz_in_Pn 1024 1744%nat then Z.of_nat 1744%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1744.
    rewrite piu_zz_inPn_1024_1743.
    rewrite piu_zz_inPn_1024_1742.
    rewrite piu_zz_inPn_1024_1741.
    rewrite piu_zz_inPn_1024_1740.
    rewrite piu_zz_inPn_1024_1739.
    rewrite piu_zz_inPn_1024_1738.
    rewrite piu_zz_inPn_1024_1737.
    rewrite piu_zz_inPn_1024_1736.
    rewrite piu_zz_inPn_1024_1735.
    rewrite piu_zz_inPn_1024_1734.
    rewrite piu_zz_inPn_1024_1733.
    rewrite piu_zz_inPn_1024_1732.
    rewrite piu_zz_inPn_1024_1731.
    rewrite piu_zz_inPn_1024_1730.
    rewrite piu_zz_inPn_1024_1729.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb20 : piu_zz_zprod_seg 1024%nat (512%nat + 1200%nat) 16%nat = ((if zz_in_Pn 1024 1713%nat then Z.of_nat 1713%nat else 1%Z) * ((if zz_in_Pn 1024 1714%nat then Z.of_nat 1714%nat else 1%Z) * ((if zz_in_Pn 1024 1715%nat then Z.of_nat 1715%nat else 1%Z) * ((if zz_in_Pn 1024 1716%nat then Z.of_nat 1716%nat else 1%Z) * ((if zz_in_Pn 1024 1717%nat then Z.of_nat 1717%nat else 1%Z) * ((if zz_in_Pn 1024 1718%nat then Z.of_nat 1718%nat else 1%Z) * ((if zz_in_Pn 1024 1719%nat then Z.of_nat 1719%nat else 1%Z) * ((if zz_in_Pn 1024 1720%nat then Z.of_nat 1720%nat else 1%Z) * ((if zz_in_Pn 1024 1721%nat then Z.of_nat 1721%nat else 1%Z) * ((if zz_in_Pn 1024 1722%nat then Z.of_nat 1722%nat else 1%Z) * ((if zz_in_Pn 1024 1723%nat then Z.of_nat 1723%nat else 1%Z) * ((if zz_in_Pn 1024 1724%nat then Z.of_nat 1724%nat else 1%Z) * ((if zz_in_Pn 1024 1725%nat then Z.of_nat 1725%nat else 1%Z) * ((if zz_in_Pn 1024 1726%nat then Z.of_nat 1726%nat else 1%Z) * ((if zz_in_Pn 1024 1727%nat then Z.of_nat 1727%nat else 1%Z) * (if zz_in_Pn 1024 1728%nat then Z.of_nat 1728%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1728.
    rewrite piu_zz_inPn_1024_1727.
    rewrite piu_zz_inPn_1024_1726.
    rewrite piu_zz_inPn_1024_1725.
    rewrite piu_zz_inPn_1024_1724.
    rewrite piu_zz_inPn_1024_1723.
    rewrite piu_zz_inPn_1024_1722.
    rewrite piu_zz_inPn_1024_1721.
    rewrite piu_zz_inPn_1024_1720.
    rewrite piu_zz_inPn_1024_1719.
    rewrite piu_zz_inPn_1024_1718.
    rewrite piu_zz_inPn_1024_1717.
    rewrite piu_zz_inPn_1024_1716.
    rewrite piu_zz_inPn_1024_1715.
    rewrite piu_zz_inPn_1024_1714.
    rewrite piu_zz_inPn_1024_1713.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb21 : piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) 16%nat = ((if zz_in_Pn 1024 1697%nat then Z.of_nat 1697%nat else 1%Z) * ((if zz_in_Pn 1024 1698%nat then Z.of_nat 1698%nat else 1%Z) * ((if zz_in_Pn 1024 1699%nat then Z.of_nat 1699%nat else 1%Z) * ((if zz_in_Pn 1024 1700%nat then Z.of_nat 1700%nat else 1%Z) * ((if zz_in_Pn 1024 1701%nat then Z.of_nat 1701%nat else 1%Z) * ((if zz_in_Pn 1024 1702%nat then Z.of_nat 1702%nat else 1%Z) * ((if zz_in_Pn 1024 1703%nat then Z.of_nat 1703%nat else 1%Z) * ((if zz_in_Pn 1024 1704%nat then Z.of_nat 1704%nat else 1%Z) * ((if zz_in_Pn 1024 1705%nat then Z.of_nat 1705%nat else 1%Z) * ((if zz_in_Pn 1024 1706%nat then Z.of_nat 1706%nat else 1%Z) * ((if zz_in_Pn 1024 1707%nat then Z.of_nat 1707%nat else 1%Z) * ((if zz_in_Pn 1024 1708%nat then Z.of_nat 1708%nat else 1%Z) * ((if zz_in_Pn 1024 1709%nat then Z.of_nat 1709%nat else 1%Z) * ((if zz_in_Pn 1024 1710%nat then Z.of_nat 1710%nat else 1%Z) * ((if zz_in_Pn 1024 1711%nat then Z.of_nat 1711%nat else 1%Z) * (if zz_in_Pn 1024 1712%nat then Z.of_nat 1712%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1712.
    rewrite piu_zz_inPn_1024_1711.
    rewrite piu_zz_inPn_1024_1710.
    rewrite piu_zz_inPn_1024_1709.
    rewrite piu_zz_inPn_1024_1708.
    rewrite piu_zz_inPn_1024_1707.
    rewrite piu_zz_inPn_1024_1706.
    rewrite piu_zz_inPn_1024_1705.
    rewrite piu_zz_inPn_1024_1704.
    rewrite piu_zz_inPn_1024_1703.
    rewrite piu_zz_inPn_1024_1702.
    rewrite piu_zz_inPn_1024_1701.
    rewrite piu_zz_inPn_1024_1700.
    rewrite piu_zz_inPn_1024_1699.
    rewrite piu_zz_inPn_1024_1698.
    rewrite piu_zz_inPn_1024_1697.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb22 : piu_zz_zprod_seg 1024%nat (512%nat + 1168%nat) 16%nat = ((if zz_in_Pn 1024 1681%nat then Z.of_nat 1681%nat else 1%Z) * ((if zz_in_Pn 1024 1682%nat then Z.of_nat 1682%nat else 1%Z) * ((if zz_in_Pn 1024 1683%nat then Z.of_nat 1683%nat else 1%Z) * ((if zz_in_Pn 1024 1684%nat then Z.of_nat 1684%nat else 1%Z) * ((if zz_in_Pn 1024 1685%nat then Z.of_nat 1685%nat else 1%Z) * ((if zz_in_Pn 1024 1686%nat then Z.of_nat 1686%nat else 1%Z) * ((if zz_in_Pn 1024 1687%nat then Z.of_nat 1687%nat else 1%Z) * ((if zz_in_Pn 1024 1688%nat then Z.of_nat 1688%nat else 1%Z) * ((if zz_in_Pn 1024 1689%nat then Z.of_nat 1689%nat else 1%Z) * ((if zz_in_Pn 1024 1690%nat then Z.of_nat 1690%nat else 1%Z) * ((if zz_in_Pn 1024 1691%nat then Z.of_nat 1691%nat else 1%Z) * ((if zz_in_Pn 1024 1692%nat then Z.of_nat 1692%nat else 1%Z) * ((if zz_in_Pn 1024 1693%nat then Z.of_nat 1693%nat else 1%Z) * ((if zz_in_Pn 1024 1694%nat then Z.of_nat 1694%nat else 1%Z) * ((if zz_in_Pn 1024 1695%nat then Z.of_nat 1695%nat else 1%Z) * (if zz_in_Pn 1024 1696%nat then Z.of_nat 1696%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1696.
    rewrite piu_zz_inPn_1024_1695.
    rewrite piu_zz_inPn_1024_1694.
    rewrite piu_zz_inPn_1024_1693.
    rewrite piu_zz_inPn_1024_1692.
    rewrite piu_zz_inPn_1024_1691.
    rewrite piu_zz_inPn_1024_1690.
    rewrite piu_zz_inPn_1024_1689.
    rewrite piu_zz_inPn_1024_1688.
    rewrite piu_zz_inPn_1024_1687.
    rewrite piu_zz_inPn_1024_1686.
    rewrite piu_zz_inPn_1024_1685.
    rewrite piu_zz_inPn_1024_1684.
    rewrite piu_zz_inPn_1024_1683.
    rewrite piu_zz_inPn_1024_1682.
    rewrite piu_zz_inPn_1024_1681.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb23 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 16%nat = ((if zz_in_Pn 1024 1665%nat then Z.of_nat 1665%nat else 1%Z) * ((if zz_in_Pn 1024 1666%nat then Z.of_nat 1666%nat else 1%Z) * ((if zz_in_Pn 1024 1667%nat then Z.of_nat 1667%nat else 1%Z) * ((if zz_in_Pn 1024 1668%nat then Z.of_nat 1668%nat else 1%Z) * ((if zz_in_Pn 1024 1669%nat then Z.of_nat 1669%nat else 1%Z) * ((if zz_in_Pn 1024 1670%nat then Z.of_nat 1670%nat else 1%Z) * ((if zz_in_Pn 1024 1671%nat then Z.of_nat 1671%nat else 1%Z) * ((if zz_in_Pn 1024 1672%nat then Z.of_nat 1672%nat else 1%Z) * ((if zz_in_Pn 1024 1673%nat then Z.of_nat 1673%nat else 1%Z) * ((if zz_in_Pn 1024 1674%nat then Z.of_nat 1674%nat else 1%Z) * ((if zz_in_Pn 1024 1675%nat then Z.of_nat 1675%nat else 1%Z) * ((if zz_in_Pn 1024 1676%nat then Z.of_nat 1676%nat else 1%Z) * ((if zz_in_Pn 1024 1677%nat then Z.of_nat 1677%nat else 1%Z) * ((if zz_in_Pn 1024 1678%nat then Z.of_nat 1678%nat else 1%Z) * ((if zz_in_Pn 1024 1679%nat then Z.of_nat 1679%nat else 1%Z) * (if zz_in_Pn 1024 1680%nat then Z.of_nat 1680%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1680.
    rewrite piu_zz_inPn_1024_1679.
    rewrite piu_zz_inPn_1024_1678.
    rewrite piu_zz_inPn_1024_1677.
    rewrite piu_zz_inPn_1024_1676.
    rewrite piu_zz_inPn_1024_1675.
    rewrite piu_zz_inPn_1024_1674.
    rewrite piu_zz_inPn_1024_1673.
    rewrite piu_zz_inPn_1024_1672.
    rewrite piu_zz_inPn_1024_1671.
    rewrite piu_zz_inPn_1024_1670.
    rewrite piu_zz_inPn_1024_1669.
    rewrite piu_zz_inPn_1024_1668.
    rewrite piu_zz_inPn_1024_1667.
    rewrite piu_zz_inPn_1024_1666.
    rewrite piu_zz_inPn_1024_1665.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb24 : piu_zz_zprod_seg 1024%nat (512%nat + 1136%nat) 16%nat = ((if zz_in_Pn 1024 1649%nat then Z.of_nat 1649%nat else 1%Z) * ((if zz_in_Pn 1024 1650%nat then Z.of_nat 1650%nat else 1%Z) * ((if zz_in_Pn 1024 1651%nat then Z.of_nat 1651%nat else 1%Z) * ((if zz_in_Pn 1024 1652%nat then Z.of_nat 1652%nat else 1%Z) * ((if zz_in_Pn 1024 1653%nat then Z.of_nat 1653%nat else 1%Z) * ((if zz_in_Pn 1024 1654%nat then Z.of_nat 1654%nat else 1%Z) * ((if zz_in_Pn 1024 1655%nat then Z.of_nat 1655%nat else 1%Z) * ((if zz_in_Pn 1024 1656%nat then Z.of_nat 1656%nat else 1%Z) * ((if zz_in_Pn 1024 1657%nat then Z.of_nat 1657%nat else 1%Z) * ((if zz_in_Pn 1024 1658%nat then Z.of_nat 1658%nat else 1%Z) * ((if zz_in_Pn 1024 1659%nat then Z.of_nat 1659%nat else 1%Z) * ((if zz_in_Pn 1024 1660%nat then Z.of_nat 1660%nat else 1%Z) * ((if zz_in_Pn 1024 1661%nat then Z.of_nat 1661%nat else 1%Z) * ((if zz_in_Pn 1024 1662%nat then Z.of_nat 1662%nat else 1%Z) * ((if zz_in_Pn 1024 1663%nat then Z.of_nat 1663%nat else 1%Z) * (if zz_in_Pn 1024 1664%nat then Z.of_nat 1664%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1664.
    rewrite piu_zz_inPn_1024_1663.
    rewrite piu_zz_inPn_1024_1662.
    rewrite piu_zz_inPn_1024_1661.
    rewrite piu_zz_inPn_1024_1660.
    rewrite piu_zz_inPn_1024_1659.
    rewrite piu_zz_inPn_1024_1658.
    rewrite piu_zz_inPn_1024_1657.
    rewrite piu_zz_inPn_1024_1656.
    rewrite piu_zz_inPn_1024_1655.
    rewrite piu_zz_inPn_1024_1654.
    rewrite piu_zz_inPn_1024_1653.
    rewrite piu_zz_inPn_1024_1652.
    rewrite piu_zz_inPn_1024_1651.
    rewrite piu_zz_inPn_1024_1650.
    rewrite piu_zz_inPn_1024_1649.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb25 : piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) 16%nat = ((if zz_in_Pn 1024 1633%nat then Z.of_nat 1633%nat else 1%Z) * ((if zz_in_Pn 1024 1634%nat then Z.of_nat 1634%nat else 1%Z) * ((if zz_in_Pn 1024 1635%nat then Z.of_nat 1635%nat else 1%Z) * ((if zz_in_Pn 1024 1636%nat then Z.of_nat 1636%nat else 1%Z) * ((if zz_in_Pn 1024 1637%nat then Z.of_nat 1637%nat else 1%Z) * ((if zz_in_Pn 1024 1638%nat then Z.of_nat 1638%nat else 1%Z) * ((if zz_in_Pn 1024 1639%nat then Z.of_nat 1639%nat else 1%Z) * ((if zz_in_Pn 1024 1640%nat then Z.of_nat 1640%nat else 1%Z) * ((if zz_in_Pn 1024 1641%nat then Z.of_nat 1641%nat else 1%Z) * ((if zz_in_Pn 1024 1642%nat then Z.of_nat 1642%nat else 1%Z) * ((if zz_in_Pn 1024 1643%nat then Z.of_nat 1643%nat else 1%Z) * ((if zz_in_Pn 1024 1644%nat then Z.of_nat 1644%nat else 1%Z) * ((if zz_in_Pn 1024 1645%nat then Z.of_nat 1645%nat else 1%Z) * ((if zz_in_Pn 1024 1646%nat then Z.of_nat 1646%nat else 1%Z) * ((if zz_in_Pn 1024 1647%nat then Z.of_nat 1647%nat else 1%Z) * (if zz_in_Pn 1024 1648%nat then Z.of_nat 1648%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1648.
    rewrite piu_zz_inPn_1024_1647.
    rewrite piu_zz_inPn_1024_1646.
    rewrite piu_zz_inPn_1024_1645.
    rewrite piu_zz_inPn_1024_1644.
    rewrite piu_zz_inPn_1024_1643.
    rewrite piu_zz_inPn_1024_1642.
    rewrite piu_zz_inPn_1024_1641.
    rewrite piu_zz_inPn_1024_1640.
    rewrite piu_zz_inPn_1024_1639.
    rewrite piu_zz_inPn_1024_1638.
    rewrite piu_zz_inPn_1024_1637.
    rewrite piu_zz_inPn_1024_1636.
    rewrite piu_zz_inPn_1024_1635.
    rewrite piu_zz_inPn_1024_1634.
    rewrite piu_zz_inPn_1024_1633.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb26 : piu_zz_zprod_seg 1024%nat (512%nat + 1104%nat) 16%nat = ((if zz_in_Pn 1024 1617%nat then Z.of_nat 1617%nat else 1%Z) * ((if zz_in_Pn 1024 1618%nat then Z.of_nat 1618%nat else 1%Z) * ((if zz_in_Pn 1024 1619%nat then Z.of_nat 1619%nat else 1%Z) * ((if zz_in_Pn 1024 1620%nat then Z.of_nat 1620%nat else 1%Z) * ((if zz_in_Pn 1024 1621%nat then Z.of_nat 1621%nat else 1%Z) * ((if zz_in_Pn 1024 1622%nat then Z.of_nat 1622%nat else 1%Z) * ((if zz_in_Pn 1024 1623%nat then Z.of_nat 1623%nat else 1%Z) * ((if zz_in_Pn 1024 1624%nat then Z.of_nat 1624%nat else 1%Z) * ((if zz_in_Pn 1024 1625%nat then Z.of_nat 1625%nat else 1%Z) * ((if zz_in_Pn 1024 1626%nat then Z.of_nat 1626%nat else 1%Z) * ((if zz_in_Pn 1024 1627%nat then Z.of_nat 1627%nat else 1%Z) * ((if zz_in_Pn 1024 1628%nat then Z.of_nat 1628%nat else 1%Z) * ((if zz_in_Pn 1024 1629%nat then Z.of_nat 1629%nat else 1%Z) * ((if zz_in_Pn 1024 1630%nat then Z.of_nat 1630%nat else 1%Z) * ((if zz_in_Pn 1024 1631%nat then Z.of_nat 1631%nat else 1%Z) * (if zz_in_Pn 1024 1632%nat then Z.of_nat 1632%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1632.
    rewrite piu_zz_inPn_1024_1631.
    rewrite piu_zz_inPn_1024_1630.
    rewrite piu_zz_inPn_1024_1629.
    rewrite piu_zz_inPn_1024_1628.
    rewrite piu_zz_inPn_1024_1627.
    rewrite piu_zz_inPn_1024_1626.
    rewrite piu_zz_inPn_1024_1625.
    rewrite piu_zz_inPn_1024_1624.
    rewrite piu_zz_inPn_1024_1623.
    rewrite piu_zz_inPn_1024_1622.
    rewrite piu_zz_inPn_1024_1621.
    rewrite piu_zz_inPn_1024_1620.
    rewrite piu_zz_inPn_1024_1619.
    rewrite piu_zz_inPn_1024_1618.
    rewrite piu_zz_inPn_1024_1617.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb27 : piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 16%nat = ((if zz_in_Pn 1024 1601%nat then Z.of_nat 1601%nat else 1%Z) * ((if zz_in_Pn 1024 1602%nat then Z.of_nat 1602%nat else 1%Z) * ((if zz_in_Pn 1024 1603%nat then Z.of_nat 1603%nat else 1%Z) * ((if zz_in_Pn 1024 1604%nat then Z.of_nat 1604%nat else 1%Z) * ((if zz_in_Pn 1024 1605%nat then Z.of_nat 1605%nat else 1%Z) * ((if zz_in_Pn 1024 1606%nat then Z.of_nat 1606%nat else 1%Z) * ((if zz_in_Pn 1024 1607%nat then Z.of_nat 1607%nat else 1%Z) * ((if zz_in_Pn 1024 1608%nat then Z.of_nat 1608%nat else 1%Z) * ((if zz_in_Pn 1024 1609%nat then Z.of_nat 1609%nat else 1%Z) * ((if zz_in_Pn 1024 1610%nat then Z.of_nat 1610%nat else 1%Z) * ((if zz_in_Pn 1024 1611%nat then Z.of_nat 1611%nat else 1%Z) * ((if zz_in_Pn 1024 1612%nat then Z.of_nat 1612%nat else 1%Z) * ((if zz_in_Pn 1024 1613%nat then Z.of_nat 1613%nat else 1%Z) * ((if zz_in_Pn 1024 1614%nat then Z.of_nat 1614%nat else 1%Z) * ((if zz_in_Pn 1024 1615%nat then Z.of_nat 1615%nat else 1%Z) * (if zz_in_Pn 1024 1616%nat then Z.of_nat 1616%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1616.
    rewrite piu_zz_inPn_1024_1615.
    rewrite piu_zz_inPn_1024_1614.
    rewrite piu_zz_inPn_1024_1613.
    rewrite piu_zz_inPn_1024_1612.
    rewrite piu_zz_inPn_1024_1611.
    rewrite piu_zz_inPn_1024_1610.
    rewrite piu_zz_inPn_1024_1609.
    rewrite piu_zz_inPn_1024_1608.
    rewrite piu_zz_inPn_1024_1607.
    rewrite piu_zz_inPn_1024_1606.
    rewrite piu_zz_inPn_1024_1605.
    rewrite piu_zz_inPn_1024_1604.
    rewrite piu_zz_inPn_1024_1603.
    rewrite piu_zz_inPn_1024_1602.
    rewrite piu_zz_inPn_1024_1601.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb28 : piu_zz_zprod_seg 1024%nat (512%nat + 1072%nat) 16%nat = ((if zz_in_Pn 1024 1585%nat then Z.of_nat 1585%nat else 1%Z) * ((if zz_in_Pn 1024 1586%nat then Z.of_nat 1586%nat else 1%Z) * ((if zz_in_Pn 1024 1587%nat then Z.of_nat 1587%nat else 1%Z) * ((if zz_in_Pn 1024 1588%nat then Z.of_nat 1588%nat else 1%Z) * ((if zz_in_Pn 1024 1589%nat then Z.of_nat 1589%nat else 1%Z) * ((if zz_in_Pn 1024 1590%nat then Z.of_nat 1590%nat else 1%Z) * ((if zz_in_Pn 1024 1591%nat then Z.of_nat 1591%nat else 1%Z) * ((if zz_in_Pn 1024 1592%nat then Z.of_nat 1592%nat else 1%Z) * ((if zz_in_Pn 1024 1593%nat then Z.of_nat 1593%nat else 1%Z) * ((if zz_in_Pn 1024 1594%nat then Z.of_nat 1594%nat else 1%Z) * ((if zz_in_Pn 1024 1595%nat then Z.of_nat 1595%nat else 1%Z) * ((if zz_in_Pn 1024 1596%nat then Z.of_nat 1596%nat else 1%Z) * ((if zz_in_Pn 1024 1597%nat then Z.of_nat 1597%nat else 1%Z) * ((if zz_in_Pn 1024 1598%nat then Z.of_nat 1598%nat else 1%Z) * ((if zz_in_Pn 1024 1599%nat then Z.of_nat 1599%nat else 1%Z) * (if zz_in_Pn 1024 1600%nat then Z.of_nat 1600%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1600.
    rewrite piu_zz_inPn_1024_1599.
    rewrite piu_zz_inPn_1024_1598.
    rewrite piu_zz_inPn_1024_1597.
    rewrite piu_zz_inPn_1024_1596.
    rewrite piu_zz_inPn_1024_1595.
    rewrite piu_zz_inPn_1024_1594.
    rewrite piu_zz_inPn_1024_1593.
    rewrite piu_zz_inPn_1024_1592.
    rewrite piu_zz_inPn_1024_1591.
    rewrite piu_zz_inPn_1024_1590.
    rewrite piu_zz_inPn_1024_1589.
    rewrite piu_zz_inPn_1024_1588.
    rewrite piu_zz_inPn_1024_1587.
    rewrite piu_zz_inPn_1024_1586.
    rewrite piu_zz_inPn_1024_1585.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb29 : piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) 16%nat = ((if zz_in_Pn 1024 1569%nat then Z.of_nat 1569%nat else 1%Z) * ((if zz_in_Pn 1024 1570%nat then Z.of_nat 1570%nat else 1%Z) * ((if zz_in_Pn 1024 1571%nat then Z.of_nat 1571%nat else 1%Z) * ((if zz_in_Pn 1024 1572%nat then Z.of_nat 1572%nat else 1%Z) * ((if zz_in_Pn 1024 1573%nat then Z.of_nat 1573%nat else 1%Z) * ((if zz_in_Pn 1024 1574%nat then Z.of_nat 1574%nat else 1%Z) * ((if zz_in_Pn 1024 1575%nat then Z.of_nat 1575%nat else 1%Z) * ((if zz_in_Pn 1024 1576%nat then Z.of_nat 1576%nat else 1%Z) * ((if zz_in_Pn 1024 1577%nat then Z.of_nat 1577%nat else 1%Z) * ((if zz_in_Pn 1024 1578%nat then Z.of_nat 1578%nat else 1%Z) * ((if zz_in_Pn 1024 1579%nat then Z.of_nat 1579%nat else 1%Z) * ((if zz_in_Pn 1024 1580%nat then Z.of_nat 1580%nat else 1%Z) * ((if zz_in_Pn 1024 1581%nat then Z.of_nat 1581%nat else 1%Z) * ((if zz_in_Pn 1024 1582%nat then Z.of_nat 1582%nat else 1%Z) * ((if zz_in_Pn 1024 1583%nat then Z.of_nat 1583%nat else 1%Z) * (if zz_in_Pn 1024 1584%nat then Z.of_nat 1584%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1584.
    rewrite piu_zz_inPn_1024_1583.
    rewrite piu_zz_inPn_1024_1582.
    rewrite piu_zz_inPn_1024_1581.
    rewrite piu_zz_inPn_1024_1580.
    rewrite piu_zz_inPn_1024_1579.
    rewrite piu_zz_inPn_1024_1578.
    rewrite piu_zz_inPn_1024_1577.
    rewrite piu_zz_inPn_1024_1576.
    rewrite piu_zz_inPn_1024_1575.
    rewrite piu_zz_inPn_1024_1574.
    rewrite piu_zz_inPn_1024_1573.
    rewrite piu_zz_inPn_1024_1572.
    rewrite piu_zz_inPn_1024_1571.
    rewrite piu_zz_inPn_1024_1570.
    rewrite piu_zz_inPn_1024_1569.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb30 : piu_zz_zprod_seg 1024%nat (512%nat + 1040%nat) 16%nat = ((if zz_in_Pn 1024 1553%nat then Z.of_nat 1553%nat else 1%Z) * ((if zz_in_Pn 1024 1554%nat then Z.of_nat 1554%nat else 1%Z) * ((if zz_in_Pn 1024 1555%nat then Z.of_nat 1555%nat else 1%Z) * ((if zz_in_Pn 1024 1556%nat then Z.of_nat 1556%nat else 1%Z) * ((if zz_in_Pn 1024 1557%nat then Z.of_nat 1557%nat else 1%Z) * ((if zz_in_Pn 1024 1558%nat then Z.of_nat 1558%nat else 1%Z) * ((if zz_in_Pn 1024 1559%nat then Z.of_nat 1559%nat else 1%Z) * ((if zz_in_Pn 1024 1560%nat then Z.of_nat 1560%nat else 1%Z) * ((if zz_in_Pn 1024 1561%nat then Z.of_nat 1561%nat else 1%Z) * ((if zz_in_Pn 1024 1562%nat then Z.of_nat 1562%nat else 1%Z) * ((if zz_in_Pn 1024 1563%nat then Z.of_nat 1563%nat else 1%Z) * ((if zz_in_Pn 1024 1564%nat then Z.of_nat 1564%nat else 1%Z) * ((if zz_in_Pn 1024 1565%nat then Z.of_nat 1565%nat else 1%Z) * ((if zz_in_Pn 1024 1566%nat then Z.of_nat 1566%nat else 1%Z) * ((if zz_in_Pn 1024 1567%nat then Z.of_nat 1567%nat else 1%Z) * (if zz_in_Pn 1024 1568%nat then Z.of_nat 1568%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1568.
    rewrite piu_zz_inPn_1024_1567.
    rewrite piu_zz_inPn_1024_1566.
    rewrite piu_zz_inPn_1024_1565.
    rewrite piu_zz_inPn_1024_1564.
    rewrite piu_zz_inPn_1024_1563.
    rewrite piu_zz_inPn_1024_1562.
    rewrite piu_zz_inPn_1024_1561.
    rewrite piu_zz_inPn_1024_1560.
    rewrite piu_zz_inPn_1024_1559.
    rewrite piu_zz_inPn_1024_1558.
    rewrite piu_zz_inPn_1024_1557.
    rewrite piu_zz_inPn_1024_1556.
    rewrite piu_zz_inPn_1024_1555.
    rewrite piu_zz_inPn_1024_1554.
    rewrite piu_zz_inPn_1024_1553.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb31 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 16%nat = ((if zz_in_Pn 1024 1537%nat then Z.of_nat 1537%nat else 1%Z) * ((if zz_in_Pn 1024 1538%nat then Z.of_nat 1538%nat else 1%Z) * ((if zz_in_Pn 1024 1539%nat then Z.of_nat 1539%nat else 1%Z) * ((if zz_in_Pn 1024 1540%nat then Z.of_nat 1540%nat else 1%Z) * ((if zz_in_Pn 1024 1541%nat then Z.of_nat 1541%nat else 1%Z) * ((if zz_in_Pn 1024 1542%nat then Z.of_nat 1542%nat else 1%Z) * ((if zz_in_Pn 1024 1543%nat then Z.of_nat 1543%nat else 1%Z) * ((if zz_in_Pn 1024 1544%nat then Z.of_nat 1544%nat else 1%Z) * ((if zz_in_Pn 1024 1545%nat then Z.of_nat 1545%nat else 1%Z) * ((if zz_in_Pn 1024 1546%nat then Z.of_nat 1546%nat else 1%Z) * ((if zz_in_Pn 1024 1547%nat then Z.of_nat 1547%nat else 1%Z) * ((if zz_in_Pn 1024 1548%nat then Z.of_nat 1548%nat else 1%Z) * ((if zz_in_Pn 1024 1549%nat then Z.of_nat 1549%nat else 1%Z) * ((if zz_in_Pn 1024 1550%nat then Z.of_nat 1550%nat else 1%Z) * ((if zz_in_Pn 1024 1551%nat then Z.of_nat 1551%nat else 1%Z) * (if zz_in_Pn 1024 1552%nat then Z.of_nat 1552%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1552.
    rewrite piu_zz_inPn_1024_1551.
    rewrite piu_zz_inPn_1024_1550.
    rewrite piu_zz_inPn_1024_1549.
    rewrite piu_zz_inPn_1024_1548.
    rewrite piu_zz_inPn_1024_1547.
    rewrite piu_zz_inPn_1024_1546.
    rewrite piu_zz_inPn_1024_1545.
    rewrite piu_zz_inPn_1024_1544.
    rewrite piu_zz_inPn_1024_1543.
    rewrite piu_zz_inPn_1024_1542.
    rewrite piu_zz_inPn_1024_1541.
    rewrite piu_zz_inPn_1024_1540.
    rewrite piu_zz_inPn_1024_1539.
    rewrite piu_zz_inPn_1024_1538.
    rewrite piu_zz_inPn_1024_1537.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb32 : piu_zz_zprod_seg 1024%nat (512%nat + 1008%nat) 16%nat = ((if zz_in_Pn 1024 1521%nat then Z.of_nat 1521%nat else 1%Z) * ((if zz_in_Pn 1024 1522%nat then Z.of_nat 1522%nat else 1%Z) * ((if zz_in_Pn 1024 1523%nat then Z.of_nat 1523%nat else 1%Z) * ((if zz_in_Pn 1024 1524%nat then Z.of_nat 1524%nat else 1%Z) * ((if zz_in_Pn 1024 1525%nat then Z.of_nat 1525%nat else 1%Z) * ((if zz_in_Pn 1024 1526%nat then Z.of_nat 1526%nat else 1%Z) * ((if zz_in_Pn 1024 1527%nat then Z.of_nat 1527%nat else 1%Z) * ((if zz_in_Pn 1024 1528%nat then Z.of_nat 1528%nat else 1%Z) * ((if zz_in_Pn 1024 1529%nat then Z.of_nat 1529%nat else 1%Z) * ((if zz_in_Pn 1024 1530%nat then Z.of_nat 1530%nat else 1%Z) * ((if zz_in_Pn 1024 1531%nat then Z.of_nat 1531%nat else 1%Z) * ((if zz_in_Pn 1024 1532%nat then Z.of_nat 1532%nat else 1%Z) * ((if zz_in_Pn 1024 1533%nat then Z.of_nat 1533%nat else 1%Z) * ((if zz_in_Pn 1024 1534%nat then Z.of_nat 1534%nat else 1%Z) * ((if zz_in_Pn 1024 1535%nat then Z.of_nat 1535%nat else 1%Z) * (if zz_in_Pn 1024 1536%nat then Z.of_nat 1536%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1536.
    rewrite piu_zz_inPn_1024_1535.
    rewrite piu_zz_inPn_1024_1534.
    rewrite piu_zz_inPn_1024_1533.
    rewrite piu_zz_inPn_1024_1532.
    rewrite piu_zz_inPn_1024_1531.
    rewrite piu_zz_inPn_1024_1530.
    rewrite piu_zz_inPn_1024_1529.
    rewrite piu_zz_inPn_1024_1528.
    rewrite piu_zz_inPn_1024_1527.
    rewrite piu_zz_inPn_1024_1526.
    rewrite piu_zz_inPn_1024_1525.
    rewrite piu_zz_inPn_1024_1524.
    rewrite piu_zz_inPn_1024_1523.
    rewrite piu_zz_inPn_1024_1522.
    rewrite piu_zz_inPn_1024_1521.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb33 : piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) 16%nat = ((if zz_in_Pn 1024 1505%nat then Z.of_nat 1505%nat else 1%Z) * ((if zz_in_Pn 1024 1506%nat then Z.of_nat 1506%nat else 1%Z) * ((if zz_in_Pn 1024 1507%nat then Z.of_nat 1507%nat else 1%Z) * ((if zz_in_Pn 1024 1508%nat then Z.of_nat 1508%nat else 1%Z) * ((if zz_in_Pn 1024 1509%nat then Z.of_nat 1509%nat else 1%Z) * ((if zz_in_Pn 1024 1510%nat then Z.of_nat 1510%nat else 1%Z) * ((if zz_in_Pn 1024 1511%nat then Z.of_nat 1511%nat else 1%Z) * ((if zz_in_Pn 1024 1512%nat then Z.of_nat 1512%nat else 1%Z) * ((if zz_in_Pn 1024 1513%nat then Z.of_nat 1513%nat else 1%Z) * ((if zz_in_Pn 1024 1514%nat then Z.of_nat 1514%nat else 1%Z) * ((if zz_in_Pn 1024 1515%nat then Z.of_nat 1515%nat else 1%Z) * ((if zz_in_Pn 1024 1516%nat then Z.of_nat 1516%nat else 1%Z) * ((if zz_in_Pn 1024 1517%nat then Z.of_nat 1517%nat else 1%Z) * ((if zz_in_Pn 1024 1518%nat then Z.of_nat 1518%nat else 1%Z) * ((if zz_in_Pn 1024 1519%nat then Z.of_nat 1519%nat else 1%Z) * (if zz_in_Pn 1024 1520%nat then Z.of_nat 1520%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1520.
    rewrite piu_zz_inPn_1024_1519.
    rewrite piu_zz_inPn_1024_1518.
    rewrite piu_zz_inPn_1024_1517.
    rewrite piu_zz_inPn_1024_1516.
    rewrite piu_zz_inPn_1024_1515.
    rewrite piu_zz_inPn_1024_1514.
    rewrite piu_zz_inPn_1024_1513.
    rewrite piu_zz_inPn_1024_1512.
    rewrite piu_zz_inPn_1024_1511.
    rewrite piu_zz_inPn_1024_1510.
    rewrite piu_zz_inPn_1024_1509.
    rewrite piu_zz_inPn_1024_1508.
    rewrite piu_zz_inPn_1024_1507.
    rewrite piu_zz_inPn_1024_1506.
    rewrite piu_zz_inPn_1024_1505.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb34 : piu_zz_zprod_seg 1024%nat (512%nat + 976%nat) 16%nat = ((if zz_in_Pn 1024 1489%nat then Z.of_nat 1489%nat else 1%Z) * ((if zz_in_Pn 1024 1490%nat then Z.of_nat 1490%nat else 1%Z) * ((if zz_in_Pn 1024 1491%nat then Z.of_nat 1491%nat else 1%Z) * ((if zz_in_Pn 1024 1492%nat then Z.of_nat 1492%nat else 1%Z) * ((if zz_in_Pn 1024 1493%nat then Z.of_nat 1493%nat else 1%Z) * ((if zz_in_Pn 1024 1494%nat then Z.of_nat 1494%nat else 1%Z) * ((if zz_in_Pn 1024 1495%nat then Z.of_nat 1495%nat else 1%Z) * ((if zz_in_Pn 1024 1496%nat then Z.of_nat 1496%nat else 1%Z) * ((if zz_in_Pn 1024 1497%nat then Z.of_nat 1497%nat else 1%Z) * ((if zz_in_Pn 1024 1498%nat then Z.of_nat 1498%nat else 1%Z) * ((if zz_in_Pn 1024 1499%nat then Z.of_nat 1499%nat else 1%Z) * ((if zz_in_Pn 1024 1500%nat then Z.of_nat 1500%nat else 1%Z) * ((if zz_in_Pn 1024 1501%nat then Z.of_nat 1501%nat else 1%Z) * ((if zz_in_Pn 1024 1502%nat then Z.of_nat 1502%nat else 1%Z) * ((if zz_in_Pn 1024 1503%nat then Z.of_nat 1503%nat else 1%Z) * (if zz_in_Pn 1024 1504%nat then Z.of_nat 1504%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1504.
    rewrite piu_zz_inPn_1024_1503.
    rewrite piu_zz_inPn_1024_1502.
    rewrite piu_zz_inPn_1024_1501.
    rewrite piu_zz_inPn_1024_1500.
    rewrite piu_zz_inPn_1024_1499.
    rewrite piu_zz_inPn_1024_1498.
    rewrite piu_zz_inPn_1024_1497.
    rewrite piu_zz_inPn_1024_1496.
    rewrite piu_zz_inPn_1024_1495.
    rewrite piu_zz_inPn_1024_1494.
    rewrite piu_zz_inPn_1024_1493.
    rewrite piu_zz_inPn_1024_1492.
    rewrite piu_zz_inPn_1024_1491.
    rewrite piu_zz_inPn_1024_1490.
    rewrite piu_zz_inPn_1024_1489.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb35 : piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 16%nat = ((if zz_in_Pn 1024 1473%nat then Z.of_nat 1473%nat else 1%Z) * ((if zz_in_Pn 1024 1474%nat then Z.of_nat 1474%nat else 1%Z) * ((if zz_in_Pn 1024 1475%nat then Z.of_nat 1475%nat else 1%Z) * ((if zz_in_Pn 1024 1476%nat then Z.of_nat 1476%nat else 1%Z) * ((if zz_in_Pn 1024 1477%nat then Z.of_nat 1477%nat else 1%Z) * ((if zz_in_Pn 1024 1478%nat then Z.of_nat 1478%nat else 1%Z) * ((if zz_in_Pn 1024 1479%nat then Z.of_nat 1479%nat else 1%Z) * ((if zz_in_Pn 1024 1480%nat then Z.of_nat 1480%nat else 1%Z) * ((if zz_in_Pn 1024 1481%nat then Z.of_nat 1481%nat else 1%Z) * ((if zz_in_Pn 1024 1482%nat then Z.of_nat 1482%nat else 1%Z) * ((if zz_in_Pn 1024 1483%nat then Z.of_nat 1483%nat else 1%Z) * ((if zz_in_Pn 1024 1484%nat then Z.of_nat 1484%nat else 1%Z) * ((if zz_in_Pn 1024 1485%nat then Z.of_nat 1485%nat else 1%Z) * ((if zz_in_Pn 1024 1486%nat then Z.of_nat 1486%nat else 1%Z) * ((if zz_in_Pn 1024 1487%nat then Z.of_nat 1487%nat else 1%Z) * (if zz_in_Pn 1024 1488%nat then Z.of_nat 1488%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1488.
    rewrite piu_zz_inPn_1024_1487.
    rewrite piu_zz_inPn_1024_1486.
    rewrite piu_zz_inPn_1024_1485.
    rewrite piu_zz_inPn_1024_1484.
    rewrite piu_zz_inPn_1024_1483.
    rewrite piu_zz_inPn_1024_1482.
    rewrite piu_zz_inPn_1024_1481.
    rewrite piu_zz_inPn_1024_1480.
    rewrite piu_zz_inPn_1024_1479.
    rewrite piu_zz_inPn_1024_1478.
    rewrite piu_zz_inPn_1024_1477.
    rewrite piu_zz_inPn_1024_1476.
    rewrite piu_zz_inPn_1024_1475.
    rewrite piu_zz_inPn_1024_1474.
    rewrite piu_zz_inPn_1024_1473.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb36 : piu_zz_zprod_seg 1024%nat (512%nat + 944%nat) 16%nat = ((if zz_in_Pn 1024 1457%nat then Z.of_nat 1457%nat else 1%Z) * ((if zz_in_Pn 1024 1458%nat then Z.of_nat 1458%nat else 1%Z) * ((if zz_in_Pn 1024 1459%nat then Z.of_nat 1459%nat else 1%Z) * ((if zz_in_Pn 1024 1460%nat then Z.of_nat 1460%nat else 1%Z) * ((if zz_in_Pn 1024 1461%nat then Z.of_nat 1461%nat else 1%Z) * ((if zz_in_Pn 1024 1462%nat then Z.of_nat 1462%nat else 1%Z) * ((if zz_in_Pn 1024 1463%nat then Z.of_nat 1463%nat else 1%Z) * ((if zz_in_Pn 1024 1464%nat then Z.of_nat 1464%nat else 1%Z) * ((if zz_in_Pn 1024 1465%nat then Z.of_nat 1465%nat else 1%Z) * ((if zz_in_Pn 1024 1466%nat then Z.of_nat 1466%nat else 1%Z) * ((if zz_in_Pn 1024 1467%nat then Z.of_nat 1467%nat else 1%Z) * ((if zz_in_Pn 1024 1468%nat then Z.of_nat 1468%nat else 1%Z) * ((if zz_in_Pn 1024 1469%nat then Z.of_nat 1469%nat else 1%Z) * ((if zz_in_Pn 1024 1470%nat then Z.of_nat 1470%nat else 1%Z) * ((if zz_in_Pn 1024 1471%nat then Z.of_nat 1471%nat else 1%Z) * (if zz_in_Pn 1024 1472%nat then Z.of_nat 1472%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1472.
    rewrite piu_zz_inPn_1024_1471.
    rewrite piu_zz_inPn_1024_1470.
    rewrite piu_zz_inPn_1024_1469.
    rewrite piu_zz_inPn_1024_1468.
    rewrite piu_zz_inPn_1024_1467.
    rewrite piu_zz_inPn_1024_1466.
    rewrite piu_zz_inPn_1024_1465.
    rewrite piu_zz_inPn_1024_1464.
    rewrite piu_zz_inPn_1024_1463.
    rewrite piu_zz_inPn_1024_1462.
    rewrite piu_zz_inPn_1024_1461.
    rewrite piu_zz_inPn_1024_1460.
    rewrite piu_zz_inPn_1024_1459.
    rewrite piu_zz_inPn_1024_1458.
    rewrite piu_zz_inPn_1024_1457.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb37 : piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) 16%nat = ((if zz_in_Pn 1024 1441%nat then Z.of_nat 1441%nat else 1%Z) * ((if zz_in_Pn 1024 1442%nat then Z.of_nat 1442%nat else 1%Z) * ((if zz_in_Pn 1024 1443%nat then Z.of_nat 1443%nat else 1%Z) * ((if zz_in_Pn 1024 1444%nat then Z.of_nat 1444%nat else 1%Z) * ((if zz_in_Pn 1024 1445%nat then Z.of_nat 1445%nat else 1%Z) * ((if zz_in_Pn 1024 1446%nat then Z.of_nat 1446%nat else 1%Z) * ((if zz_in_Pn 1024 1447%nat then Z.of_nat 1447%nat else 1%Z) * ((if zz_in_Pn 1024 1448%nat then Z.of_nat 1448%nat else 1%Z) * ((if zz_in_Pn 1024 1449%nat then Z.of_nat 1449%nat else 1%Z) * ((if zz_in_Pn 1024 1450%nat then Z.of_nat 1450%nat else 1%Z) * ((if zz_in_Pn 1024 1451%nat then Z.of_nat 1451%nat else 1%Z) * ((if zz_in_Pn 1024 1452%nat then Z.of_nat 1452%nat else 1%Z) * ((if zz_in_Pn 1024 1453%nat then Z.of_nat 1453%nat else 1%Z) * ((if zz_in_Pn 1024 1454%nat then Z.of_nat 1454%nat else 1%Z) * ((if zz_in_Pn 1024 1455%nat then Z.of_nat 1455%nat else 1%Z) * (if zz_in_Pn 1024 1456%nat then Z.of_nat 1456%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1456.
    rewrite piu_zz_inPn_1024_1455.
    rewrite piu_zz_inPn_1024_1454.
    rewrite piu_zz_inPn_1024_1453.
    rewrite piu_zz_inPn_1024_1452.
    rewrite piu_zz_inPn_1024_1451.
    rewrite piu_zz_inPn_1024_1450.
    rewrite piu_zz_inPn_1024_1449.
    rewrite piu_zz_inPn_1024_1448.
    rewrite piu_zz_inPn_1024_1447.
    rewrite piu_zz_inPn_1024_1446.
    rewrite piu_zz_inPn_1024_1445.
    rewrite piu_zz_inPn_1024_1444.
    rewrite piu_zz_inPn_1024_1443.
    rewrite piu_zz_inPn_1024_1442.
    rewrite piu_zz_inPn_1024_1441.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb38 : piu_zz_zprod_seg 1024%nat (512%nat + 912%nat) 16%nat = ((if zz_in_Pn 1024 1425%nat then Z.of_nat 1425%nat else 1%Z) * ((if zz_in_Pn 1024 1426%nat then Z.of_nat 1426%nat else 1%Z) * ((if zz_in_Pn 1024 1427%nat then Z.of_nat 1427%nat else 1%Z) * ((if zz_in_Pn 1024 1428%nat then Z.of_nat 1428%nat else 1%Z) * ((if zz_in_Pn 1024 1429%nat then Z.of_nat 1429%nat else 1%Z) * ((if zz_in_Pn 1024 1430%nat then Z.of_nat 1430%nat else 1%Z) * ((if zz_in_Pn 1024 1431%nat then Z.of_nat 1431%nat else 1%Z) * ((if zz_in_Pn 1024 1432%nat then Z.of_nat 1432%nat else 1%Z) * ((if zz_in_Pn 1024 1433%nat then Z.of_nat 1433%nat else 1%Z) * ((if zz_in_Pn 1024 1434%nat then Z.of_nat 1434%nat else 1%Z) * ((if zz_in_Pn 1024 1435%nat then Z.of_nat 1435%nat else 1%Z) * ((if zz_in_Pn 1024 1436%nat then Z.of_nat 1436%nat else 1%Z) * ((if zz_in_Pn 1024 1437%nat then Z.of_nat 1437%nat else 1%Z) * ((if zz_in_Pn 1024 1438%nat then Z.of_nat 1438%nat else 1%Z) * ((if zz_in_Pn 1024 1439%nat then Z.of_nat 1439%nat else 1%Z) * (if zz_in_Pn 1024 1440%nat then Z.of_nat 1440%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1440.
    rewrite piu_zz_inPn_1024_1439.
    rewrite piu_zz_inPn_1024_1438.
    rewrite piu_zz_inPn_1024_1437.
    rewrite piu_zz_inPn_1024_1436.
    rewrite piu_zz_inPn_1024_1435.
    rewrite piu_zz_inPn_1024_1434.
    rewrite piu_zz_inPn_1024_1433.
    rewrite piu_zz_inPn_1024_1432.
    rewrite piu_zz_inPn_1024_1431.
    rewrite piu_zz_inPn_1024_1430.
    rewrite piu_zz_inPn_1024_1429.
    rewrite piu_zz_inPn_1024_1428.
    rewrite piu_zz_inPn_1024_1427.
    rewrite piu_zz_inPn_1024_1426.
    rewrite piu_zz_inPn_1024_1425.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb39 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 16%nat = ((if zz_in_Pn 1024 1409%nat then Z.of_nat 1409%nat else 1%Z) * ((if zz_in_Pn 1024 1410%nat then Z.of_nat 1410%nat else 1%Z) * ((if zz_in_Pn 1024 1411%nat then Z.of_nat 1411%nat else 1%Z) * ((if zz_in_Pn 1024 1412%nat then Z.of_nat 1412%nat else 1%Z) * ((if zz_in_Pn 1024 1413%nat then Z.of_nat 1413%nat else 1%Z) * ((if zz_in_Pn 1024 1414%nat then Z.of_nat 1414%nat else 1%Z) * ((if zz_in_Pn 1024 1415%nat then Z.of_nat 1415%nat else 1%Z) * ((if zz_in_Pn 1024 1416%nat then Z.of_nat 1416%nat else 1%Z) * ((if zz_in_Pn 1024 1417%nat then Z.of_nat 1417%nat else 1%Z) * ((if zz_in_Pn 1024 1418%nat then Z.of_nat 1418%nat else 1%Z) * ((if zz_in_Pn 1024 1419%nat then Z.of_nat 1419%nat else 1%Z) * ((if zz_in_Pn 1024 1420%nat then Z.of_nat 1420%nat else 1%Z) * ((if zz_in_Pn 1024 1421%nat then Z.of_nat 1421%nat else 1%Z) * ((if zz_in_Pn 1024 1422%nat then Z.of_nat 1422%nat else 1%Z) * ((if zz_in_Pn 1024 1423%nat then Z.of_nat 1423%nat else 1%Z) * (if zz_in_Pn 1024 1424%nat then Z.of_nat 1424%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1424.
    rewrite piu_zz_inPn_1024_1423.
    rewrite piu_zz_inPn_1024_1422.
    rewrite piu_zz_inPn_1024_1421.
    rewrite piu_zz_inPn_1024_1420.
    rewrite piu_zz_inPn_1024_1419.
    rewrite piu_zz_inPn_1024_1418.
    rewrite piu_zz_inPn_1024_1417.
    rewrite piu_zz_inPn_1024_1416.
    rewrite piu_zz_inPn_1024_1415.
    rewrite piu_zz_inPn_1024_1414.
    rewrite piu_zz_inPn_1024_1413.
    rewrite piu_zz_inPn_1024_1412.
    rewrite piu_zz_inPn_1024_1411.
    rewrite piu_zz_inPn_1024_1410.
    rewrite piu_zz_inPn_1024_1409.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb40 : piu_zz_zprod_seg 1024%nat (512%nat + 880%nat) 16%nat = ((if zz_in_Pn 1024 1393%nat then Z.of_nat 1393%nat else 1%Z) * ((if zz_in_Pn 1024 1394%nat then Z.of_nat 1394%nat else 1%Z) * ((if zz_in_Pn 1024 1395%nat then Z.of_nat 1395%nat else 1%Z) * ((if zz_in_Pn 1024 1396%nat then Z.of_nat 1396%nat else 1%Z) * ((if zz_in_Pn 1024 1397%nat then Z.of_nat 1397%nat else 1%Z) * ((if zz_in_Pn 1024 1398%nat then Z.of_nat 1398%nat else 1%Z) * ((if zz_in_Pn 1024 1399%nat then Z.of_nat 1399%nat else 1%Z) * ((if zz_in_Pn 1024 1400%nat then Z.of_nat 1400%nat else 1%Z) * ((if zz_in_Pn 1024 1401%nat then Z.of_nat 1401%nat else 1%Z) * ((if zz_in_Pn 1024 1402%nat then Z.of_nat 1402%nat else 1%Z) * ((if zz_in_Pn 1024 1403%nat then Z.of_nat 1403%nat else 1%Z) * ((if zz_in_Pn 1024 1404%nat then Z.of_nat 1404%nat else 1%Z) * ((if zz_in_Pn 1024 1405%nat then Z.of_nat 1405%nat else 1%Z) * ((if zz_in_Pn 1024 1406%nat then Z.of_nat 1406%nat else 1%Z) * ((if zz_in_Pn 1024 1407%nat then Z.of_nat 1407%nat else 1%Z) * (if zz_in_Pn 1024 1408%nat then Z.of_nat 1408%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1408.
    rewrite piu_zz_inPn_1024_1407.
    rewrite piu_zz_inPn_1024_1406.
    rewrite piu_zz_inPn_1024_1405.
    rewrite piu_zz_inPn_1024_1404.
    rewrite piu_zz_inPn_1024_1403.
    rewrite piu_zz_inPn_1024_1402.
    rewrite piu_zz_inPn_1024_1401.
    rewrite piu_zz_inPn_1024_1400.
    rewrite piu_zz_inPn_1024_1399.
    rewrite piu_zz_inPn_1024_1398.
    rewrite piu_zz_inPn_1024_1397.
    rewrite piu_zz_inPn_1024_1396.
    rewrite piu_zz_inPn_1024_1395.
    rewrite piu_zz_inPn_1024_1394.
    rewrite piu_zz_inPn_1024_1393.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb41 : piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) 16%nat = ((if zz_in_Pn 1024 1377%nat then Z.of_nat 1377%nat else 1%Z) * ((if zz_in_Pn 1024 1378%nat then Z.of_nat 1378%nat else 1%Z) * ((if zz_in_Pn 1024 1379%nat then Z.of_nat 1379%nat else 1%Z) * ((if zz_in_Pn 1024 1380%nat then Z.of_nat 1380%nat else 1%Z) * ((if zz_in_Pn 1024 1381%nat then Z.of_nat 1381%nat else 1%Z) * ((if zz_in_Pn 1024 1382%nat then Z.of_nat 1382%nat else 1%Z) * ((if zz_in_Pn 1024 1383%nat then Z.of_nat 1383%nat else 1%Z) * ((if zz_in_Pn 1024 1384%nat then Z.of_nat 1384%nat else 1%Z) * ((if zz_in_Pn 1024 1385%nat then Z.of_nat 1385%nat else 1%Z) * ((if zz_in_Pn 1024 1386%nat then Z.of_nat 1386%nat else 1%Z) * ((if zz_in_Pn 1024 1387%nat then Z.of_nat 1387%nat else 1%Z) * ((if zz_in_Pn 1024 1388%nat then Z.of_nat 1388%nat else 1%Z) * ((if zz_in_Pn 1024 1389%nat then Z.of_nat 1389%nat else 1%Z) * ((if zz_in_Pn 1024 1390%nat then Z.of_nat 1390%nat else 1%Z) * ((if zz_in_Pn 1024 1391%nat then Z.of_nat 1391%nat else 1%Z) * (if zz_in_Pn 1024 1392%nat then Z.of_nat 1392%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1392.
    rewrite piu_zz_inPn_1024_1391.
    rewrite piu_zz_inPn_1024_1390.
    rewrite piu_zz_inPn_1024_1389.
    rewrite piu_zz_inPn_1024_1388.
    rewrite piu_zz_inPn_1024_1387.
    rewrite piu_zz_inPn_1024_1386.
    rewrite piu_zz_inPn_1024_1385.
    rewrite piu_zz_inPn_1024_1384.
    rewrite piu_zz_inPn_1024_1383.
    rewrite piu_zz_inPn_1024_1382.
    rewrite piu_zz_inPn_1024_1381.
    rewrite piu_zz_inPn_1024_1380.
    rewrite piu_zz_inPn_1024_1379.
    rewrite piu_zz_inPn_1024_1378.
    rewrite piu_zz_inPn_1024_1377.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb42 : piu_zz_zprod_seg 1024%nat (512%nat + 848%nat) 16%nat = ((if zz_in_Pn 1024 1361%nat then Z.of_nat 1361%nat else 1%Z) * ((if zz_in_Pn 1024 1362%nat then Z.of_nat 1362%nat else 1%Z) * ((if zz_in_Pn 1024 1363%nat then Z.of_nat 1363%nat else 1%Z) * ((if zz_in_Pn 1024 1364%nat then Z.of_nat 1364%nat else 1%Z) * ((if zz_in_Pn 1024 1365%nat then Z.of_nat 1365%nat else 1%Z) * ((if zz_in_Pn 1024 1366%nat then Z.of_nat 1366%nat else 1%Z) * ((if zz_in_Pn 1024 1367%nat then Z.of_nat 1367%nat else 1%Z) * ((if zz_in_Pn 1024 1368%nat then Z.of_nat 1368%nat else 1%Z) * ((if zz_in_Pn 1024 1369%nat then Z.of_nat 1369%nat else 1%Z) * ((if zz_in_Pn 1024 1370%nat then Z.of_nat 1370%nat else 1%Z) * ((if zz_in_Pn 1024 1371%nat then Z.of_nat 1371%nat else 1%Z) * ((if zz_in_Pn 1024 1372%nat then Z.of_nat 1372%nat else 1%Z) * ((if zz_in_Pn 1024 1373%nat then Z.of_nat 1373%nat else 1%Z) * ((if zz_in_Pn 1024 1374%nat then Z.of_nat 1374%nat else 1%Z) * ((if zz_in_Pn 1024 1375%nat then Z.of_nat 1375%nat else 1%Z) * (if zz_in_Pn 1024 1376%nat then Z.of_nat 1376%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1376.
    rewrite piu_zz_inPn_1024_1375.
    rewrite piu_zz_inPn_1024_1374.
    rewrite piu_zz_inPn_1024_1373.
    rewrite piu_zz_inPn_1024_1372.
    rewrite piu_zz_inPn_1024_1371.
    rewrite piu_zz_inPn_1024_1370.
    rewrite piu_zz_inPn_1024_1369.
    rewrite piu_zz_inPn_1024_1368.
    rewrite piu_zz_inPn_1024_1367.
    rewrite piu_zz_inPn_1024_1366.
    rewrite piu_zz_inPn_1024_1365.
    rewrite piu_zz_inPn_1024_1364.
    rewrite piu_zz_inPn_1024_1363.
    rewrite piu_zz_inPn_1024_1362.
    rewrite piu_zz_inPn_1024_1361.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb43 : piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 16%nat = ((if zz_in_Pn 1024 1345%nat then Z.of_nat 1345%nat else 1%Z) * ((if zz_in_Pn 1024 1346%nat then Z.of_nat 1346%nat else 1%Z) * ((if zz_in_Pn 1024 1347%nat then Z.of_nat 1347%nat else 1%Z) * ((if zz_in_Pn 1024 1348%nat then Z.of_nat 1348%nat else 1%Z) * ((if zz_in_Pn 1024 1349%nat then Z.of_nat 1349%nat else 1%Z) * ((if zz_in_Pn 1024 1350%nat then Z.of_nat 1350%nat else 1%Z) * ((if zz_in_Pn 1024 1351%nat then Z.of_nat 1351%nat else 1%Z) * ((if zz_in_Pn 1024 1352%nat then Z.of_nat 1352%nat else 1%Z) * ((if zz_in_Pn 1024 1353%nat then Z.of_nat 1353%nat else 1%Z) * ((if zz_in_Pn 1024 1354%nat then Z.of_nat 1354%nat else 1%Z) * ((if zz_in_Pn 1024 1355%nat then Z.of_nat 1355%nat else 1%Z) * ((if zz_in_Pn 1024 1356%nat then Z.of_nat 1356%nat else 1%Z) * ((if zz_in_Pn 1024 1357%nat then Z.of_nat 1357%nat else 1%Z) * ((if zz_in_Pn 1024 1358%nat then Z.of_nat 1358%nat else 1%Z) * ((if zz_in_Pn 1024 1359%nat then Z.of_nat 1359%nat else 1%Z) * (if zz_in_Pn 1024 1360%nat then Z.of_nat 1360%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1360.
    rewrite piu_zz_inPn_1024_1359.
    rewrite piu_zz_inPn_1024_1358.
    rewrite piu_zz_inPn_1024_1357.
    rewrite piu_zz_inPn_1024_1356.
    rewrite piu_zz_inPn_1024_1355.
    rewrite piu_zz_inPn_1024_1354.
    rewrite piu_zz_inPn_1024_1353.
    rewrite piu_zz_inPn_1024_1352.
    rewrite piu_zz_inPn_1024_1351.
    rewrite piu_zz_inPn_1024_1350.
    rewrite piu_zz_inPn_1024_1349.
    rewrite piu_zz_inPn_1024_1348.
    rewrite piu_zz_inPn_1024_1347.
    rewrite piu_zz_inPn_1024_1346.
    rewrite piu_zz_inPn_1024_1345.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb44 : piu_zz_zprod_seg 1024%nat (512%nat + 816%nat) 16%nat = ((if zz_in_Pn 1024 1329%nat then Z.of_nat 1329%nat else 1%Z) * ((if zz_in_Pn 1024 1330%nat then Z.of_nat 1330%nat else 1%Z) * ((if zz_in_Pn 1024 1331%nat then Z.of_nat 1331%nat else 1%Z) * ((if zz_in_Pn 1024 1332%nat then Z.of_nat 1332%nat else 1%Z) * ((if zz_in_Pn 1024 1333%nat then Z.of_nat 1333%nat else 1%Z) * ((if zz_in_Pn 1024 1334%nat then Z.of_nat 1334%nat else 1%Z) * ((if zz_in_Pn 1024 1335%nat then Z.of_nat 1335%nat else 1%Z) * ((if zz_in_Pn 1024 1336%nat then Z.of_nat 1336%nat else 1%Z) * ((if zz_in_Pn 1024 1337%nat then Z.of_nat 1337%nat else 1%Z) * ((if zz_in_Pn 1024 1338%nat then Z.of_nat 1338%nat else 1%Z) * ((if zz_in_Pn 1024 1339%nat then Z.of_nat 1339%nat else 1%Z) * ((if zz_in_Pn 1024 1340%nat then Z.of_nat 1340%nat else 1%Z) * ((if zz_in_Pn 1024 1341%nat then Z.of_nat 1341%nat else 1%Z) * ((if zz_in_Pn 1024 1342%nat then Z.of_nat 1342%nat else 1%Z) * ((if zz_in_Pn 1024 1343%nat then Z.of_nat 1343%nat else 1%Z) * (if zz_in_Pn 1024 1344%nat then Z.of_nat 1344%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1344.
    rewrite piu_zz_inPn_1024_1343.
    rewrite piu_zz_inPn_1024_1342.
    rewrite piu_zz_inPn_1024_1341.
    rewrite piu_zz_inPn_1024_1340.
    rewrite piu_zz_inPn_1024_1339.
    rewrite piu_zz_inPn_1024_1338.
    rewrite piu_zz_inPn_1024_1337.
    rewrite piu_zz_inPn_1024_1336.
    rewrite piu_zz_inPn_1024_1335.
    rewrite piu_zz_inPn_1024_1334.
    rewrite piu_zz_inPn_1024_1333.
    rewrite piu_zz_inPn_1024_1332.
    rewrite piu_zz_inPn_1024_1331.
    rewrite piu_zz_inPn_1024_1330.
    rewrite piu_zz_inPn_1024_1329.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb45 : piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) 16%nat = ((if zz_in_Pn 1024 1313%nat then Z.of_nat 1313%nat else 1%Z) * ((if zz_in_Pn 1024 1314%nat then Z.of_nat 1314%nat else 1%Z) * ((if zz_in_Pn 1024 1315%nat then Z.of_nat 1315%nat else 1%Z) * ((if zz_in_Pn 1024 1316%nat then Z.of_nat 1316%nat else 1%Z) * ((if zz_in_Pn 1024 1317%nat then Z.of_nat 1317%nat else 1%Z) * ((if zz_in_Pn 1024 1318%nat then Z.of_nat 1318%nat else 1%Z) * ((if zz_in_Pn 1024 1319%nat then Z.of_nat 1319%nat else 1%Z) * ((if zz_in_Pn 1024 1320%nat then Z.of_nat 1320%nat else 1%Z) * ((if zz_in_Pn 1024 1321%nat then Z.of_nat 1321%nat else 1%Z) * ((if zz_in_Pn 1024 1322%nat then Z.of_nat 1322%nat else 1%Z) * ((if zz_in_Pn 1024 1323%nat then Z.of_nat 1323%nat else 1%Z) * ((if zz_in_Pn 1024 1324%nat then Z.of_nat 1324%nat else 1%Z) * ((if zz_in_Pn 1024 1325%nat then Z.of_nat 1325%nat else 1%Z) * ((if zz_in_Pn 1024 1326%nat then Z.of_nat 1326%nat else 1%Z) * ((if zz_in_Pn 1024 1327%nat then Z.of_nat 1327%nat else 1%Z) * (if zz_in_Pn 1024 1328%nat then Z.of_nat 1328%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1328.
    rewrite piu_zz_inPn_1024_1327.
    rewrite piu_zz_inPn_1024_1326.
    rewrite piu_zz_inPn_1024_1325.
    rewrite piu_zz_inPn_1024_1324.
    rewrite piu_zz_inPn_1024_1323.
    rewrite piu_zz_inPn_1024_1322.
    rewrite piu_zz_inPn_1024_1321.
    rewrite piu_zz_inPn_1024_1320.
    rewrite piu_zz_inPn_1024_1319.
    rewrite piu_zz_inPn_1024_1318.
    rewrite piu_zz_inPn_1024_1317.
    rewrite piu_zz_inPn_1024_1316.
    rewrite piu_zz_inPn_1024_1315.
    rewrite piu_zz_inPn_1024_1314.
    rewrite piu_zz_inPn_1024_1313.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb46 : piu_zz_zprod_seg 1024%nat (512%nat + 784%nat) 16%nat = ((if zz_in_Pn 1024 1297%nat then Z.of_nat 1297%nat else 1%Z) * ((if zz_in_Pn 1024 1298%nat then Z.of_nat 1298%nat else 1%Z) * ((if zz_in_Pn 1024 1299%nat then Z.of_nat 1299%nat else 1%Z) * ((if zz_in_Pn 1024 1300%nat then Z.of_nat 1300%nat else 1%Z) * ((if zz_in_Pn 1024 1301%nat then Z.of_nat 1301%nat else 1%Z) * ((if zz_in_Pn 1024 1302%nat then Z.of_nat 1302%nat else 1%Z) * ((if zz_in_Pn 1024 1303%nat then Z.of_nat 1303%nat else 1%Z) * ((if zz_in_Pn 1024 1304%nat then Z.of_nat 1304%nat else 1%Z) * ((if zz_in_Pn 1024 1305%nat then Z.of_nat 1305%nat else 1%Z) * ((if zz_in_Pn 1024 1306%nat then Z.of_nat 1306%nat else 1%Z) * ((if zz_in_Pn 1024 1307%nat then Z.of_nat 1307%nat else 1%Z) * ((if zz_in_Pn 1024 1308%nat then Z.of_nat 1308%nat else 1%Z) * ((if zz_in_Pn 1024 1309%nat then Z.of_nat 1309%nat else 1%Z) * ((if zz_in_Pn 1024 1310%nat then Z.of_nat 1310%nat else 1%Z) * ((if zz_in_Pn 1024 1311%nat then Z.of_nat 1311%nat else 1%Z) * (if zz_in_Pn 1024 1312%nat then Z.of_nat 1312%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1312.
    rewrite piu_zz_inPn_1024_1311.
    rewrite piu_zz_inPn_1024_1310.
    rewrite piu_zz_inPn_1024_1309.
    rewrite piu_zz_inPn_1024_1308.
    rewrite piu_zz_inPn_1024_1307.
    rewrite piu_zz_inPn_1024_1306.
    rewrite piu_zz_inPn_1024_1305.
    rewrite piu_zz_inPn_1024_1304.
    rewrite piu_zz_inPn_1024_1303.
    rewrite piu_zz_inPn_1024_1302.
    rewrite piu_zz_inPn_1024_1301.
    rewrite piu_zz_inPn_1024_1300.
    rewrite piu_zz_inPn_1024_1299.
    rewrite piu_zz_inPn_1024_1298.
    rewrite piu_zz_inPn_1024_1297.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb47 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 16%nat = ((if zz_in_Pn 1024 1281%nat then Z.of_nat 1281%nat else 1%Z) * ((if zz_in_Pn 1024 1282%nat then Z.of_nat 1282%nat else 1%Z) * ((if zz_in_Pn 1024 1283%nat then Z.of_nat 1283%nat else 1%Z) * ((if zz_in_Pn 1024 1284%nat then Z.of_nat 1284%nat else 1%Z) * ((if zz_in_Pn 1024 1285%nat then Z.of_nat 1285%nat else 1%Z) * ((if zz_in_Pn 1024 1286%nat then Z.of_nat 1286%nat else 1%Z) * ((if zz_in_Pn 1024 1287%nat then Z.of_nat 1287%nat else 1%Z) * ((if zz_in_Pn 1024 1288%nat then Z.of_nat 1288%nat else 1%Z) * ((if zz_in_Pn 1024 1289%nat then Z.of_nat 1289%nat else 1%Z) * ((if zz_in_Pn 1024 1290%nat then Z.of_nat 1290%nat else 1%Z) * ((if zz_in_Pn 1024 1291%nat then Z.of_nat 1291%nat else 1%Z) * ((if zz_in_Pn 1024 1292%nat then Z.of_nat 1292%nat else 1%Z) * ((if zz_in_Pn 1024 1293%nat then Z.of_nat 1293%nat else 1%Z) * ((if zz_in_Pn 1024 1294%nat then Z.of_nat 1294%nat else 1%Z) * ((if zz_in_Pn 1024 1295%nat then Z.of_nat 1295%nat else 1%Z) * (if zz_in_Pn 1024 1296%nat then Z.of_nat 1296%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1296.
    rewrite piu_zz_inPn_1024_1295.
    rewrite piu_zz_inPn_1024_1294.
    rewrite piu_zz_inPn_1024_1293.
    rewrite piu_zz_inPn_1024_1292.
    rewrite piu_zz_inPn_1024_1291.
    rewrite piu_zz_inPn_1024_1290.
    rewrite piu_zz_inPn_1024_1289.
    rewrite piu_zz_inPn_1024_1288.
    rewrite piu_zz_inPn_1024_1287.
    rewrite piu_zz_inPn_1024_1286.
    rewrite piu_zz_inPn_1024_1285.
    rewrite piu_zz_inPn_1024_1284.
    rewrite piu_zz_inPn_1024_1283.
    rewrite piu_zz_inPn_1024_1282.
    rewrite piu_zz_inPn_1024_1281.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb48 : piu_zz_zprod_seg 1024%nat (512%nat + 752%nat) 16%nat = ((if zz_in_Pn 1024 1265%nat then Z.of_nat 1265%nat else 1%Z) * ((if zz_in_Pn 1024 1266%nat then Z.of_nat 1266%nat else 1%Z) * ((if zz_in_Pn 1024 1267%nat then Z.of_nat 1267%nat else 1%Z) * ((if zz_in_Pn 1024 1268%nat then Z.of_nat 1268%nat else 1%Z) * ((if zz_in_Pn 1024 1269%nat then Z.of_nat 1269%nat else 1%Z) * ((if zz_in_Pn 1024 1270%nat then Z.of_nat 1270%nat else 1%Z) * ((if zz_in_Pn 1024 1271%nat then Z.of_nat 1271%nat else 1%Z) * ((if zz_in_Pn 1024 1272%nat then Z.of_nat 1272%nat else 1%Z) * ((if zz_in_Pn 1024 1273%nat then Z.of_nat 1273%nat else 1%Z) * ((if zz_in_Pn 1024 1274%nat then Z.of_nat 1274%nat else 1%Z) * ((if zz_in_Pn 1024 1275%nat then Z.of_nat 1275%nat else 1%Z) * ((if zz_in_Pn 1024 1276%nat then Z.of_nat 1276%nat else 1%Z) * ((if zz_in_Pn 1024 1277%nat then Z.of_nat 1277%nat else 1%Z) * ((if zz_in_Pn 1024 1278%nat then Z.of_nat 1278%nat else 1%Z) * ((if zz_in_Pn 1024 1279%nat then Z.of_nat 1279%nat else 1%Z) * (if zz_in_Pn 1024 1280%nat then Z.of_nat 1280%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1280.
    rewrite piu_zz_inPn_1024_1279.
    rewrite piu_zz_inPn_1024_1278.
    rewrite piu_zz_inPn_1024_1277.
    rewrite piu_zz_inPn_1024_1276.
    rewrite piu_zz_inPn_1024_1275.
    rewrite piu_zz_inPn_1024_1274.
    rewrite piu_zz_inPn_1024_1273.
    rewrite piu_zz_inPn_1024_1272.
    rewrite piu_zz_inPn_1024_1271.
    rewrite piu_zz_inPn_1024_1270.
    rewrite piu_zz_inPn_1024_1269.
    rewrite piu_zz_inPn_1024_1268.
    rewrite piu_zz_inPn_1024_1267.
    rewrite piu_zz_inPn_1024_1266.
    rewrite piu_zz_inPn_1024_1265.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb49 : piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) 16%nat = ((if zz_in_Pn 1024 1249%nat then Z.of_nat 1249%nat else 1%Z) * ((if zz_in_Pn 1024 1250%nat then Z.of_nat 1250%nat else 1%Z) * ((if zz_in_Pn 1024 1251%nat then Z.of_nat 1251%nat else 1%Z) * ((if zz_in_Pn 1024 1252%nat then Z.of_nat 1252%nat else 1%Z) * ((if zz_in_Pn 1024 1253%nat then Z.of_nat 1253%nat else 1%Z) * ((if zz_in_Pn 1024 1254%nat then Z.of_nat 1254%nat else 1%Z) * ((if zz_in_Pn 1024 1255%nat then Z.of_nat 1255%nat else 1%Z) * ((if zz_in_Pn 1024 1256%nat then Z.of_nat 1256%nat else 1%Z) * ((if zz_in_Pn 1024 1257%nat then Z.of_nat 1257%nat else 1%Z) * ((if zz_in_Pn 1024 1258%nat then Z.of_nat 1258%nat else 1%Z) * ((if zz_in_Pn 1024 1259%nat then Z.of_nat 1259%nat else 1%Z) * ((if zz_in_Pn 1024 1260%nat then Z.of_nat 1260%nat else 1%Z) * ((if zz_in_Pn 1024 1261%nat then Z.of_nat 1261%nat else 1%Z) * ((if zz_in_Pn 1024 1262%nat then Z.of_nat 1262%nat else 1%Z) * ((if zz_in_Pn 1024 1263%nat then Z.of_nat 1263%nat else 1%Z) * (if zz_in_Pn 1024 1264%nat then Z.of_nat 1264%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1264.
    rewrite piu_zz_inPn_1024_1263.
    rewrite piu_zz_inPn_1024_1262.
    rewrite piu_zz_inPn_1024_1261.
    rewrite piu_zz_inPn_1024_1260.
    rewrite piu_zz_inPn_1024_1259.
    rewrite piu_zz_inPn_1024_1258.
    rewrite piu_zz_inPn_1024_1257.
    rewrite piu_zz_inPn_1024_1256.
    rewrite piu_zz_inPn_1024_1255.
    rewrite piu_zz_inPn_1024_1254.
    rewrite piu_zz_inPn_1024_1253.
    rewrite piu_zz_inPn_1024_1252.
    rewrite piu_zz_inPn_1024_1251.
    rewrite piu_zz_inPn_1024_1250.
    rewrite piu_zz_inPn_1024_1249.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb50 : piu_zz_zprod_seg 1024%nat (512%nat + 720%nat) 16%nat = ((if zz_in_Pn 1024 1233%nat then Z.of_nat 1233%nat else 1%Z) * ((if zz_in_Pn 1024 1234%nat then Z.of_nat 1234%nat else 1%Z) * ((if zz_in_Pn 1024 1235%nat then Z.of_nat 1235%nat else 1%Z) * ((if zz_in_Pn 1024 1236%nat then Z.of_nat 1236%nat else 1%Z) * ((if zz_in_Pn 1024 1237%nat then Z.of_nat 1237%nat else 1%Z) * ((if zz_in_Pn 1024 1238%nat then Z.of_nat 1238%nat else 1%Z) * ((if zz_in_Pn 1024 1239%nat then Z.of_nat 1239%nat else 1%Z) * ((if zz_in_Pn 1024 1240%nat then Z.of_nat 1240%nat else 1%Z) * ((if zz_in_Pn 1024 1241%nat then Z.of_nat 1241%nat else 1%Z) * ((if zz_in_Pn 1024 1242%nat then Z.of_nat 1242%nat else 1%Z) * ((if zz_in_Pn 1024 1243%nat then Z.of_nat 1243%nat else 1%Z) * ((if zz_in_Pn 1024 1244%nat then Z.of_nat 1244%nat else 1%Z) * ((if zz_in_Pn 1024 1245%nat then Z.of_nat 1245%nat else 1%Z) * ((if zz_in_Pn 1024 1246%nat then Z.of_nat 1246%nat else 1%Z) * ((if zz_in_Pn 1024 1247%nat then Z.of_nat 1247%nat else 1%Z) * (if zz_in_Pn 1024 1248%nat then Z.of_nat 1248%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1248.
    rewrite piu_zz_inPn_1024_1247.
    rewrite piu_zz_inPn_1024_1246.
    rewrite piu_zz_inPn_1024_1245.
    rewrite piu_zz_inPn_1024_1244.
    rewrite piu_zz_inPn_1024_1243.
    rewrite piu_zz_inPn_1024_1242.
    rewrite piu_zz_inPn_1024_1241.
    rewrite piu_zz_inPn_1024_1240.
    rewrite piu_zz_inPn_1024_1239.
    rewrite piu_zz_inPn_1024_1238.
    rewrite piu_zz_inPn_1024_1237.
    rewrite piu_zz_inPn_1024_1236.
    rewrite piu_zz_inPn_1024_1235.
    rewrite piu_zz_inPn_1024_1234.
    rewrite piu_zz_inPn_1024_1233.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb51 : piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 16%nat = ((if zz_in_Pn 1024 1217%nat then Z.of_nat 1217%nat else 1%Z) * ((if zz_in_Pn 1024 1218%nat then Z.of_nat 1218%nat else 1%Z) * ((if zz_in_Pn 1024 1219%nat then Z.of_nat 1219%nat else 1%Z) * ((if zz_in_Pn 1024 1220%nat then Z.of_nat 1220%nat else 1%Z) * ((if zz_in_Pn 1024 1221%nat then Z.of_nat 1221%nat else 1%Z) * ((if zz_in_Pn 1024 1222%nat then Z.of_nat 1222%nat else 1%Z) * ((if zz_in_Pn 1024 1223%nat then Z.of_nat 1223%nat else 1%Z) * ((if zz_in_Pn 1024 1224%nat then Z.of_nat 1224%nat else 1%Z) * ((if zz_in_Pn 1024 1225%nat then Z.of_nat 1225%nat else 1%Z) * ((if zz_in_Pn 1024 1226%nat then Z.of_nat 1226%nat else 1%Z) * ((if zz_in_Pn 1024 1227%nat then Z.of_nat 1227%nat else 1%Z) * ((if zz_in_Pn 1024 1228%nat then Z.of_nat 1228%nat else 1%Z) * ((if zz_in_Pn 1024 1229%nat then Z.of_nat 1229%nat else 1%Z) * ((if zz_in_Pn 1024 1230%nat then Z.of_nat 1230%nat else 1%Z) * ((if zz_in_Pn 1024 1231%nat then Z.of_nat 1231%nat else 1%Z) * (if zz_in_Pn 1024 1232%nat then Z.of_nat 1232%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1232.
    rewrite piu_zz_inPn_1024_1231.
    rewrite piu_zz_inPn_1024_1230.
    rewrite piu_zz_inPn_1024_1229.
    rewrite piu_zz_inPn_1024_1228.
    rewrite piu_zz_inPn_1024_1227.
    rewrite piu_zz_inPn_1024_1226.
    rewrite piu_zz_inPn_1024_1225.
    rewrite piu_zz_inPn_1024_1224.
    rewrite piu_zz_inPn_1024_1223.
    rewrite piu_zz_inPn_1024_1222.
    rewrite piu_zz_inPn_1024_1221.
    rewrite piu_zz_inPn_1024_1220.
    rewrite piu_zz_inPn_1024_1219.
    rewrite piu_zz_inPn_1024_1218.
    rewrite piu_zz_inPn_1024_1217.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb52 : piu_zz_zprod_seg 1024%nat (512%nat + 688%nat) 16%nat = ((if zz_in_Pn 1024 1201%nat then Z.of_nat 1201%nat else 1%Z) * ((if zz_in_Pn 1024 1202%nat then Z.of_nat 1202%nat else 1%Z) * ((if zz_in_Pn 1024 1203%nat then Z.of_nat 1203%nat else 1%Z) * ((if zz_in_Pn 1024 1204%nat then Z.of_nat 1204%nat else 1%Z) * ((if zz_in_Pn 1024 1205%nat then Z.of_nat 1205%nat else 1%Z) * ((if zz_in_Pn 1024 1206%nat then Z.of_nat 1206%nat else 1%Z) * ((if zz_in_Pn 1024 1207%nat then Z.of_nat 1207%nat else 1%Z) * ((if zz_in_Pn 1024 1208%nat then Z.of_nat 1208%nat else 1%Z) * ((if zz_in_Pn 1024 1209%nat then Z.of_nat 1209%nat else 1%Z) * ((if zz_in_Pn 1024 1210%nat then Z.of_nat 1210%nat else 1%Z) * ((if zz_in_Pn 1024 1211%nat then Z.of_nat 1211%nat else 1%Z) * ((if zz_in_Pn 1024 1212%nat then Z.of_nat 1212%nat else 1%Z) * ((if zz_in_Pn 1024 1213%nat then Z.of_nat 1213%nat else 1%Z) * ((if zz_in_Pn 1024 1214%nat then Z.of_nat 1214%nat else 1%Z) * ((if zz_in_Pn 1024 1215%nat then Z.of_nat 1215%nat else 1%Z) * (if zz_in_Pn 1024 1216%nat then Z.of_nat 1216%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1216.
    rewrite piu_zz_inPn_1024_1215.
    rewrite piu_zz_inPn_1024_1214.
    rewrite piu_zz_inPn_1024_1213.
    rewrite piu_zz_inPn_1024_1212.
    rewrite piu_zz_inPn_1024_1211.
    rewrite piu_zz_inPn_1024_1210.
    rewrite piu_zz_inPn_1024_1209.
    rewrite piu_zz_inPn_1024_1208.
    rewrite piu_zz_inPn_1024_1207.
    rewrite piu_zz_inPn_1024_1206.
    rewrite piu_zz_inPn_1024_1205.
    rewrite piu_zz_inPn_1024_1204.
    rewrite piu_zz_inPn_1024_1203.
    rewrite piu_zz_inPn_1024_1202.
    rewrite piu_zz_inPn_1024_1201.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb53 : piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) 16%nat = ((if zz_in_Pn 1024 1185%nat then Z.of_nat 1185%nat else 1%Z) * ((if zz_in_Pn 1024 1186%nat then Z.of_nat 1186%nat else 1%Z) * ((if zz_in_Pn 1024 1187%nat then Z.of_nat 1187%nat else 1%Z) * ((if zz_in_Pn 1024 1188%nat then Z.of_nat 1188%nat else 1%Z) * ((if zz_in_Pn 1024 1189%nat then Z.of_nat 1189%nat else 1%Z) * ((if zz_in_Pn 1024 1190%nat then Z.of_nat 1190%nat else 1%Z) * ((if zz_in_Pn 1024 1191%nat then Z.of_nat 1191%nat else 1%Z) * ((if zz_in_Pn 1024 1192%nat then Z.of_nat 1192%nat else 1%Z) * ((if zz_in_Pn 1024 1193%nat then Z.of_nat 1193%nat else 1%Z) * ((if zz_in_Pn 1024 1194%nat then Z.of_nat 1194%nat else 1%Z) * ((if zz_in_Pn 1024 1195%nat then Z.of_nat 1195%nat else 1%Z) * ((if zz_in_Pn 1024 1196%nat then Z.of_nat 1196%nat else 1%Z) * ((if zz_in_Pn 1024 1197%nat then Z.of_nat 1197%nat else 1%Z) * ((if zz_in_Pn 1024 1198%nat then Z.of_nat 1198%nat else 1%Z) * ((if zz_in_Pn 1024 1199%nat then Z.of_nat 1199%nat else 1%Z) * (if zz_in_Pn 1024 1200%nat then Z.of_nat 1200%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1200.
    rewrite piu_zz_inPn_1024_1199.
    rewrite piu_zz_inPn_1024_1198.
    rewrite piu_zz_inPn_1024_1197.
    rewrite piu_zz_inPn_1024_1196.
    rewrite piu_zz_inPn_1024_1195.
    rewrite piu_zz_inPn_1024_1194.
    rewrite piu_zz_inPn_1024_1193.
    rewrite piu_zz_inPn_1024_1192.
    rewrite piu_zz_inPn_1024_1191.
    rewrite piu_zz_inPn_1024_1190.
    rewrite piu_zz_inPn_1024_1189.
    rewrite piu_zz_inPn_1024_1188.
    rewrite piu_zz_inPn_1024_1187.
    rewrite piu_zz_inPn_1024_1186.
    rewrite piu_zz_inPn_1024_1185.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb54 : piu_zz_zprod_seg 1024%nat (512%nat + 656%nat) 16%nat = ((if zz_in_Pn 1024 1169%nat then Z.of_nat 1169%nat else 1%Z) * ((if zz_in_Pn 1024 1170%nat then Z.of_nat 1170%nat else 1%Z) * ((if zz_in_Pn 1024 1171%nat then Z.of_nat 1171%nat else 1%Z) * ((if zz_in_Pn 1024 1172%nat then Z.of_nat 1172%nat else 1%Z) * ((if zz_in_Pn 1024 1173%nat then Z.of_nat 1173%nat else 1%Z) * ((if zz_in_Pn 1024 1174%nat then Z.of_nat 1174%nat else 1%Z) * ((if zz_in_Pn 1024 1175%nat then Z.of_nat 1175%nat else 1%Z) * ((if zz_in_Pn 1024 1176%nat then Z.of_nat 1176%nat else 1%Z) * ((if zz_in_Pn 1024 1177%nat then Z.of_nat 1177%nat else 1%Z) * ((if zz_in_Pn 1024 1178%nat then Z.of_nat 1178%nat else 1%Z) * ((if zz_in_Pn 1024 1179%nat then Z.of_nat 1179%nat else 1%Z) * ((if zz_in_Pn 1024 1180%nat then Z.of_nat 1180%nat else 1%Z) * ((if zz_in_Pn 1024 1181%nat then Z.of_nat 1181%nat else 1%Z) * ((if zz_in_Pn 1024 1182%nat then Z.of_nat 1182%nat else 1%Z) * ((if zz_in_Pn 1024 1183%nat then Z.of_nat 1183%nat else 1%Z) * (if zz_in_Pn 1024 1184%nat then Z.of_nat 1184%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1184.
    rewrite piu_zz_inPn_1024_1183.
    rewrite piu_zz_inPn_1024_1182.
    rewrite piu_zz_inPn_1024_1181.
    rewrite piu_zz_inPn_1024_1180.
    rewrite piu_zz_inPn_1024_1179.
    rewrite piu_zz_inPn_1024_1178.
    rewrite piu_zz_inPn_1024_1177.
    rewrite piu_zz_inPn_1024_1176.
    rewrite piu_zz_inPn_1024_1175.
    rewrite piu_zz_inPn_1024_1174.
    rewrite piu_zz_inPn_1024_1173.
    rewrite piu_zz_inPn_1024_1172.
    rewrite piu_zz_inPn_1024_1171.
    rewrite piu_zz_inPn_1024_1170.
    rewrite piu_zz_inPn_1024_1169.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb55 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 16%nat = ((if zz_in_Pn 1024 1153%nat then Z.of_nat 1153%nat else 1%Z) * ((if zz_in_Pn 1024 1154%nat then Z.of_nat 1154%nat else 1%Z) * ((if zz_in_Pn 1024 1155%nat then Z.of_nat 1155%nat else 1%Z) * ((if zz_in_Pn 1024 1156%nat then Z.of_nat 1156%nat else 1%Z) * ((if zz_in_Pn 1024 1157%nat then Z.of_nat 1157%nat else 1%Z) * ((if zz_in_Pn 1024 1158%nat then Z.of_nat 1158%nat else 1%Z) * ((if zz_in_Pn 1024 1159%nat then Z.of_nat 1159%nat else 1%Z) * ((if zz_in_Pn 1024 1160%nat then Z.of_nat 1160%nat else 1%Z) * ((if zz_in_Pn 1024 1161%nat then Z.of_nat 1161%nat else 1%Z) * ((if zz_in_Pn 1024 1162%nat then Z.of_nat 1162%nat else 1%Z) * ((if zz_in_Pn 1024 1163%nat then Z.of_nat 1163%nat else 1%Z) * ((if zz_in_Pn 1024 1164%nat then Z.of_nat 1164%nat else 1%Z) * ((if zz_in_Pn 1024 1165%nat then Z.of_nat 1165%nat else 1%Z) * ((if zz_in_Pn 1024 1166%nat then Z.of_nat 1166%nat else 1%Z) * ((if zz_in_Pn 1024 1167%nat then Z.of_nat 1167%nat else 1%Z) * (if zz_in_Pn 1024 1168%nat then Z.of_nat 1168%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1168.
    rewrite piu_zz_inPn_1024_1167.
    rewrite piu_zz_inPn_1024_1166.
    rewrite piu_zz_inPn_1024_1165.
    rewrite piu_zz_inPn_1024_1164.
    rewrite piu_zz_inPn_1024_1163.
    rewrite piu_zz_inPn_1024_1162.
    rewrite piu_zz_inPn_1024_1161.
    rewrite piu_zz_inPn_1024_1160.
    rewrite piu_zz_inPn_1024_1159.
    rewrite piu_zz_inPn_1024_1158.
    rewrite piu_zz_inPn_1024_1157.
    rewrite piu_zz_inPn_1024_1156.
    rewrite piu_zz_inPn_1024_1155.
    rewrite piu_zz_inPn_1024_1154.
    rewrite piu_zz_inPn_1024_1153.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb56 : piu_zz_zprod_seg 1024%nat (512%nat + 624%nat) 16%nat = ((if zz_in_Pn 1024 1137%nat then Z.of_nat 1137%nat else 1%Z) * ((if zz_in_Pn 1024 1138%nat then Z.of_nat 1138%nat else 1%Z) * ((if zz_in_Pn 1024 1139%nat then Z.of_nat 1139%nat else 1%Z) * ((if zz_in_Pn 1024 1140%nat then Z.of_nat 1140%nat else 1%Z) * ((if zz_in_Pn 1024 1141%nat then Z.of_nat 1141%nat else 1%Z) * ((if zz_in_Pn 1024 1142%nat then Z.of_nat 1142%nat else 1%Z) * ((if zz_in_Pn 1024 1143%nat then Z.of_nat 1143%nat else 1%Z) * ((if zz_in_Pn 1024 1144%nat then Z.of_nat 1144%nat else 1%Z) * ((if zz_in_Pn 1024 1145%nat then Z.of_nat 1145%nat else 1%Z) * ((if zz_in_Pn 1024 1146%nat then Z.of_nat 1146%nat else 1%Z) * ((if zz_in_Pn 1024 1147%nat then Z.of_nat 1147%nat else 1%Z) * ((if zz_in_Pn 1024 1148%nat then Z.of_nat 1148%nat else 1%Z) * ((if zz_in_Pn 1024 1149%nat then Z.of_nat 1149%nat else 1%Z) * ((if zz_in_Pn 1024 1150%nat then Z.of_nat 1150%nat else 1%Z) * ((if zz_in_Pn 1024 1151%nat then Z.of_nat 1151%nat else 1%Z) * (if zz_in_Pn 1024 1152%nat then Z.of_nat 1152%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1152.
    rewrite piu_zz_inPn_1024_1151.
    rewrite piu_zz_inPn_1024_1150.
    rewrite piu_zz_inPn_1024_1149.
    rewrite piu_zz_inPn_1024_1148.
    rewrite piu_zz_inPn_1024_1147.
    rewrite piu_zz_inPn_1024_1146.
    rewrite piu_zz_inPn_1024_1145.
    rewrite piu_zz_inPn_1024_1144.
    rewrite piu_zz_inPn_1024_1143.
    rewrite piu_zz_inPn_1024_1142.
    rewrite piu_zz_inPn_1024_1141.
    rewrite piu_zz_inPn_1024_1140.
    rewrite piu_zz_inPn_1024_1139.
    rewrite piu_zz_inPn_1024_1138.
    rewrite piu_zz_inPn_1024_1137.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb57 : piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) 16%nat = ((if zz_in_Pn 1024 1121%nat then Z.of_nat 1121%nat else 1%Z) * ((if zz_in_Pn 1024 1122%nat then Z.of_nat 1122%nat else 1%Z) * ((if zz_in_Pn 1024 1123%nat then Z.of_nat 1123%nat else 1%Z) * ((if zz_in_Pn 1024 1124%nat then Z.of_nat 1124%nat else 1%Z) * ((if zz_in_Pn 1024 1125%nat then Z.of_nat 1125%nat else 1%Z) * ((if zz_in_Pn 1024 1126%nat then Z.of_nat 1126%nat else 1%Z) * ((if zz_in_Pn 1024 1127%nat then Z.of_nat 1127%nat else 1%Z) * ((if zz_in_Pn 1024 1128%nat then Z.of_nat 1128%nat else 1%Z) * ((if zz_in_Pn 1024 1129%nat then Z.of_nat 1129%nat else 1%Z) * ((if zz_in_Pn 1024 1130%nat then Z.of_nat 1130%nat else 1%Z) * ((if zz_in_Pn 1024 1131%nat then Z.of_nat 1131%nat else 1%Z) * ((if zz_in_Pn 1024 1132%nat then Z.of_nat 1132%nat else 1%Z) * ((if zz_in_Pn 1024 1133%nat then Z.of_nat 1133%nat else 1%Z) * ((if zz_in_Pn 1024 1134%nat then Z.of_nat 1134%nat else 1%Z) * ((if zz_in_Pn 1024 1135%nat then Z.of_nat 1135%nat else 1%Z) * (if zz_in_Pn 1024 1136%nat then Z.of_nat 1136%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1136.
    rewrite piu_zz_inPn_1024_1135.
    rewrite piu_zz_inPn_1024_1134.
    rewrite piu_zz_inPn_1024_1133.
    rewrite piu_zz_inPn_1024_1132.
    rewrite piu_zz_inPn_1024_1131.
    rewrite piu_zz_inPn_1024_1130.
    rewrite piu_zz_inPn_1024_1129.
    rewrite piu_zz_inPn_1024_1128.
    rewrite piu_zz_inPn_1024_1127.
    rewrite piu_zz_inPn_1024_1126.
    rewrite piu_zz_inPn_1024_1125.
    rewrite piu_zz_inPn_1024_1124.
    rewrite piu_zz_inPn_1024_1123.
    rewrite piu_zz_inPn_1024_1122.
    rewrite piu_zz_inPn_1024_1121.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb58 : piu_zz_zprod_seg 1024%nat (512%nat + 592%nat) 16%nat = ((if zz_in_Pn 1024 1105%nat then Z.of_nat 1105%nat else 1%Z) * ((if zz_in_Pn 1024 1106%nat then Z.of_nat 1106%nat else 1%Z) * ((if zz_in_Pn 1024 1107%nat then Z.of_nat 1107%nat else 1%Z) * ((if zz_in_Pn 1024 1108%nat then Z.of_nat 1108%nat else 1%Z) * ((if zz_in_Pn 1024 1109%nat then Z.of_nat 1109%nat else 1%Z) * ((if zz_in_Pn 1024 1110%nat then Z.of_nat 1110%nat else 1%Z) * ((if zz_in_Pn 1024 1111%nat then Z.of_nat 1111%nat else 1%Z) * ((if zz_in_Pn 1024 1112%nat then Z.of_nat 1112%nat else 1%Z) * ((if zz_in_Pn 1024 1113%nat then Z.of_nat 1113%nat else 1%Z) * ((if zz_in_Pn 1024 1114%nat then Z.of_nat 1114%nat else 1%Z) * ((if zz_in_Pn 1024 1115%nat then Z.of_nat 1115%nat else 1%Z) * ((if zz_in_Pn 1024 1116%nat then Z.of_nat 1116%nat else 1%Z) * ((if zz_in_Pn 1024 1117%nat then Z.of_nat 1117%nat else 1%Z) * ((if zz_in_Pn 1024 1118%nat then Z.of_nat 1118%nat else 1%Z) * ((if zz_in_Pn 1024 1119%nat then Z.of_nat 1119%nat else 1%Z) * (if zz_in_Pn 1024 1120%nat then Z.of_nat 1120%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1120.
    rewrite piu_zz_inPn_1024_1119.
    rewrite piu_zz_inPn_1024_1118.
    rewrite piu_zz_inPn_1024_1117.
    rewrite piu_zz_inPn_1024_1116.
    rewrite piu_zz_inPn_1024_1115.
    rewrite piu_zz_inPn_1024_1114.
    rewrite piu_zz_inPn_1024_1113.
    rewrite piu_zz_inPn_1024_1112.
    rewrite piu_zz_inPn_1024_1111.
    rewrite piu_zz_inPn_1024_1110.
    rewrite piu_zz_inPn_1024_1109.
    rewrite piu_zz_inPn_1024_1108.
    rewrite piu_zz_inPn_1024_1107.
    rewrite piu_zz_inPn_1024_1106.
    rewrite piu_zz_inPn_1024_1105.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb59 : piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 16%nat = ((if zz_in_Pn 1024 1089%nat then Z.of_nat 1089%nat else 1%Z) * ((if zz_in_Pn 1024 1090%nat then Z.of_nat 1090%nat else 1%Z) * ((if zz_in_Pn 1024 1091%nat then Z.of_nat 1091%nat else 1%Z) * ((if zz_in_Pn 1024 1092%nat then Z.of_nat 1092%nat else 1%Z) * ((if zz_in_Pn 1024 1093%nat then Z.of_nat 1093%nat else 1%Z) * ((if zz_in_Pn 1024 1094%nat then Z.of_nat 1094%nat else 1%Z) * ((if zz_in_Pn 1024 1095%nat then Z.of_nat 1095%nat else 1%Z) * ((if zz_in_Pn 1024 1096%nat then Z.of_nat 1096%nat else 1%Z) * ((if zz_in_Pn 1024 1097%nat then Z.of_nat 1097%nat else 1%Z) * ((if zz_in_Pn 1024 1098%nat then Z.of_nat 1098%nat else 1%Z) * ((if zz_in_Pn 1024 1099%nat then Z.of_nat 1099%nat else 1%Z) * ((if zz_in_Pn 1024 1100%nat then Z.of_nat 1100%nat else 1%Z) * ((if zz_in_Pn 1024 1101%nat then Z.of_nat 1101%nat else 1%Z) * ((if zz_in_Pn 1024 1102%nat then Z.of_nat 1102%nat else 1%Z) * ((if zz_in_Pn 1024 1103%nat then Z.of_nat 1103%nat else 1%Z) * (if zz_in_Pn 1024 1104%nat then Z.of_nat 1104%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1104.
    rewrite piu_zz_inPn_1024_1103.
    rewrite piu_zz_inPn_1024_1102.
    rewrite piu_zz_inPn_1024_1101.
    rewrite piu_zz_inPn_1024_1100.
    rewrite piu_zz_inPn_1024_1099.
    rewrite piu_zz_inPn_1024_1098.
    rewrite piu_zz_inPn_1024_1097.
    rewrite piu_zz_inPn_1024_1096.
    rewrite piu_zz_inPn_1024_1095.
    rewrite piu_zz_inPn_1024_1094.
    rewrite piu_zz_inPn_1024_1093.
    rewrite piu_zz_inPn_1024_1092.
    rewrite piu_zz_inPn_1024_1091.
    rewrite piu_zz_inPn_1024_1090.
    rewrite piu_zz_inPn_1024_1089.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb60 : piu_zz_zprod_seg 1024%nat (512%nat + 560%nat) 16%nat = ((if zz_in_Pn 1024 1073%nat then Z.of_nat 1073%nat else 1%Z) * ((if zz_in_Pn 1024 1074%nat then Z.of_nat 1074%nat else 1%Z) * ((if zz_in_Pn 1024 1075%nat then Z.of_nat 1075%nat else 1%Z) * ((if zz_in_Pn 1024 1076%nat then Z.of_nat 1076%nat else 1%Z) * ((if zz_in_Pn 1024 1077%nat then Z.of_nat 1077%nat else 1%Z) * ((if zz_in_Pn 1024 1078%nat then Z.of_nat 1078%nat else 1%Z) * ((if zz_in_Pn 1024 1079%nat then Z.of_nat 1079%nat else 1%Z) * ((if zz_in_Pn 1024 1080%nat then Z.of_nat 1080%nat else 1%Z) * ((if zz_in_Pn 1024 1081%nat then Z.of_nat 1081%nat else 1%Z) * ((if zz_in_Pn 1024 1082%nat then Z.of_nat 1082%nat else 1%Z) * ((if zz_in_Pn 1024 1083%nat then Z.of_nat 1083%nat else 1%Z) * ((if zz_in_Pn 1024 1084%nat then Z.of_nat 1084%nat else 1%Z) * ((if zz_in_Pn 1024 1085%nat then Z.of_nat 1085%nat else 1%Z) * ((if zz_in_Pn 1024 1086%nat then Z.of_nat 1086%nat else 1%Z) * ((if zz_in_Pn 1024 1087%nat then Z.of_nat 1087%nat else 1%Z) * (if zz_in_Pn 1024 1088%nat then Z.of_nat 1088%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1088.
    rewrite piu_zz_inPn_1024_1087.
    rewrite piu_zz_inPn_1024_1086.
    rewrite piu_zz_inPn_1024_1085.
    rewrite piu_zz_inPn_1024_1084.
    rewrite piu_zz_inPn_1024_1083.
    rewrite piu_zz_inPn_1024_1082.
    rewrite piu_zz_inPn_1024_1081.
    rewrite piu_zz_inPn_1024_1080.
    rewrite piu_zz_inPn_1024_1079.
    rewrite piu_zz_inPn_1024_1078.
    rewrite piu_zz_inPn_1024_1077.
    rewrite piu_zz_inPn_1024_1076.
    rewrite piu_zz_inPn_1024_1075.
    rewrite piu_zz_inPn_1024_1074.
    rewrite piu_zz_inPn_1024_1073.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb61 : piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) 16%nat = ((if zz_in_Pn 1024 1057%nat then Z.of_nat 1057%nat else 1%Z) * ((if zz_in_Pn 1024 1058%nat then Z.of_nat 1058%nat else 1%Z) * ((if zz_in_Pn 1024 1059%nat then Z.of_nat 1059%nat else 1%Z) * ((if zz_in_Pn 1024 1060%nat then Z.of_nat 1060%nat else 1%Z) * ((if zz_in_Pn 1024 1061%nat then Z.of_nat 1061%nat else 1%Z) * ((if zz_in_Pn 1024 1062%nat then Z.of_nat 1062%nat else 1%Z) * ((if zz_in_Pn 1024 1063%nat then Z.of_nat 1063%nat else 1%Z) * ((if zz_in_Pn 1024 1064%nat then Z.of_nat 1064%nat else 1%Z) * ((if zz_in_Pn 1024 1065%nat then Z.of_nat 1065%nat else 1%Z) * ((if zz_in_Pn 1024 1066%nat then Z.of_nat 1066%nat else 1%Z) * ((if zz_in_Pn 1024 1067%nat then Z.of_nat 1067%nat else 1%Z) * ((if zz_in_Pn 1024 1068%nat then Z.of_nat 1068%nat else 1%Z) * ((if zz_in_Pn 1024 1069%nat then Z.of_nat 1069%nat else 1%Z) * ((if zz_in_Pn 1024 1070%nat then Z.of_nat 1070%nat else 1%Z) * ((if zz_in_Pn 1024 1071%nat then Z.of_nat 1071%nat else 1%Z) * (if zz_in_Pn 1024 1072%nat then Z.of_nat 1072%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1072.
    rewrite piu_zz_inPn_1024_1071.
    rewrite piu_zz_inPn_1024_1070.
    rewrite piu_zz_inPn_1024_1069.
    rewrite piu_zz_inPn_1024_1068.
    rewrite piu_zz_inPn_1024_1067.
    rewrite piu_zz_inPn_1024_1066.
    rewrite piu_zz_inPn_1024_1065.
    rewrite piu_zz_inPn_1024_1064.
    rewrite piu_zz_inPn_1024_1063.
    rewrite piu_zz_inPn_1024_1062.
    rewrite piu_zz_inPn_1024_1061.
    rewrite piu_zz_inPn_1024_1060.
    rewrite piu_zz_inPn_1024_1059.
    rewrite piu_zz_inPn_1024_1058.
    rewrite piu_zz_inPn_1024_1057.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb62 : piu_zz_zprod_seg 1024%nat (512%nat + 528%nat) 16%nat = ((if zz_in_Pn 1024 1041%nat then Z.of_nat 1041%nat else 1%Z) * ((if zz_in_Pn 1024 1042%nat then Z.of_nat 1042%nat else 1%Z) * ((if zz_in_Pn 1024 1043%nat then Z.of_nat 1043%nat else 1%Z) * ((if zz_in_Pn 1024 1044%nat then Z.of_nat 1044%nat else 1%Z) * ((if zz_in_Pn 1024 1045%nat then Z.of_nat 1045%nat else 1%Z) * ((if zz_in_Pn 1024 1046%nat then Z.of_nat 1046%nat else 1%Z) * ((if zz_in_Pn 1024 1047%nat then Z.of_nat 1047%nat else 1%Z) * ((if zz_in_Pn 1024 1048%nat then Z.of_nat 1048%nat else 1%Z) * ((if zz_in_Pn 1024 1049%nat then Z.of_nat 1049%nat else 1%Z) * ((if zz_in_Pn 1024 1050%nat then Z.of_nat 1050%nat else 1%Z) * ((if zz_in_Pn 1024 1051%nat then Z.of_nat 1051%nat else 1%Z) * ((if zz_in_Pn 1024 1052%nat then Z.of_nat 1052%nat else 1%Z) * ((if zz_in_Pn 1024 1053%nat then Z.of_nat 1053%nat else 1%Z) * ((if zz_in_Pn 1024 1054%nat then Z.of_nat 1054%nat else 1%Z) * ((if zz_in_Pn 1024 1055%nat then Z.of_nat 1055%nat else 1%Z) * (if zz_in_Pn 1024 1056%nat then Z.of_nat 1056%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1056.
    rewrite piu_zz_inPn_1024_1055.
    rewrite piu_zz_inPn_1024_1054.
    rewrite piu_zz_inPn_1024_1053.
    rewrite piu_zz_inPn_1024_1052.
    rewrite piu_zz_inPn_1024_1051.
    rewrite piu_zz_inPn_1024_1050.
    rewrite piu_zz_inPn_1024_1049.
    rewrite piu_zz_inPn_1024_1048.
    rewrite piu_zz_inPn_1024_1047.
    rewrite piu_zz_inPn_1024_1046.
    rewrite piu_zz_inPn_1024_1045.
    rewrite piu_zz_inPn_1024_1044.
    rewrite piu_zz_inPn_1024_1043.
    rewrite piu_zz_inPn_1024_1042.
    rewrite piu_zz_inPn_1024_1041.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb63 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 16%nat = ((if zz_in_Pn 1024 1025%nat then Z.of_nat 1025%nat else 1%Z) * ((if zz_in_Pn 1024 1026%nat then Z.of_nat 1026%nat else 1%Z) * ((if zz_in_Pn 1024 1027%nat then Z.of_nat 1027%nat else 1%Z) * ((if zz_in_Pn 1024 1028%nat then Z.of_nat 1028%nat else 1%Z) * ((if zz_in_Pn 1024 1029%nat then Z.of_nat 1029%nat else 1%Z) * ((if zz_in_Pn 1024 1030%nat then Z.of_nat 1030%nat else 1%Z) * ((if zz_in_Pn 1024 1031%nat then Z.of_nat 1031%nat else 1%Z) * ((if zz_in_Pn 1024 1032%nat then Z.of_nat 1032%nat else 1%Z) * ((if zz_in_Pn 1024 1033%nat then Z.of_nat 1033%nat else 1%Z) * ((if zz_in_Pn 1024 1034%nat then Z.of_nat 1034%nat else 1%Z) * ((if zz_in_Pn 1024 1035%nat then Z.of_nat 1035%nat else 1%Z) * ((if zz_in_Pn 1024 1036%nat then Z.of_nat 1036%nat else 1%Z) * ((if zz_in_Pn 1024 1037%nat then Z.of_nat 1037%nat else 1%Z) * ((if zz_in_Pn 1024 1038%nat then Z.of_nat 1038%nat else 1%Z) * ((if zz_in_Pn 1024 1039%nat then Z.of_nat 1039%nat else 1%Z) * (if zz_in_Pn 1024 1040%nat then Z.of_nat 1040%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1040.
    rewrite piu_zz_inPn_1024_1039.
    rewrite piu_zz_inPn_1024_1038.
    rewrite piu_zz_inPn_1024_1037.
    rewrite piu_zz_inPn_1024_1036.
    rewrite piu_zz_inPn_1024_1035.
    rewrite piu_zz_inPn_1024_1034.
    rewrite piu_zz_inPn_1024_1033.
    rewrite piu_zz_inPn_1024_1032.
    rewrite piu_zz_inPn_1024_1031.
    rewrite piu_zz_inPn_1024_1030.
    rewrite piu_zz_inPn_1024_1029.
    rewrite piu_zz_inPn_1024_1028.
    rewrite piu_zz_inPn_1024_1027.
    rewrite piu_zz_inPn_1024_1026.
    rewrite piu_zz_inPn_1024_1025.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb64 : piu_zz_zprod_seg 1024%nat (512%nat + 496%nat) 16%nat = ((if zz_in_Pn 1024 1009%nat then Z.of_nat 1009%nat else 1%Z) * ((if zz_in_Pn 1024 1010%nat then Z.of_nat 1010%nat else 1%Z) * ((if zz_in_Pn 1024 1011%nat then Z.of_nat 1011%nat else 1%Z) * ((if zz_in_Pn 1024 1012%nat then Z.of_nat 1012%nat else 1%Z) * ((if zz_in_Pn 1024 1013%nat then Z.of_nat 1013%nat else 1%Z) * ((if zz_in_Pn 1024 1014%nat then Z.of_nat 1014%nat else 1%Z) * ((if zz_in_Pn 1024 1015%nat then Z.of_nat 1015%nat else 1%Z) * ((if zz_in_Pn 1024 1016%nat then Z.of_nat 1016%nat else 1%Z) * ((if zz_in_Pn 1024 1017%nat then Z.of_nat 1017%nat else 1%Z) * ((if zz_in_Pn 1024 1018%nat then Z.of_nat 1018%nat else 1%Z) * ((if zz_in_Pn 1024 1019%nat then Z.of_nat 1019%nat else 1%Z) * ((if zz_in_Pn 1024 1020%nat then Z.of_nat 1020%nat else 1%Z) * ((if zz_in_Pn 1024 1021%nat then Z.of_nat 1021%nat else 1%Z) * ((if zz_in_Pn 1024 1022%nat then Z.of_nat 1022%nat else 1%Z) * ((if zz_in_Pn 1024 1023%nat then Z.of_nat 1023%nat else 1%Z) * (if zz_in_Pn 1024 1024%nat then Z.of_nat 1024%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1024.
    rewrite piu_zz_inPn_1024_1023.
    rewrite piu_zz_inPn_1024_1022.
    rewrite piu_zz_inPn_1024_1021.
    rewrite piu_zz_inPn_1024_1020.
    rewrite piu_zz_inPn_1024_1019.
    rewrite piu_zz_inPn_1024_1018.
    rewrite piu_zz_inPn_1024_1017.
    rewrite piu_zz_inPn_1024_1016.
    rewrite piu_zz_inPn_1024_1015.
    rewrite piu_zz_inPn_1024_1014.
    rewrite piu_zz_inPn_1024_1013.
    rewrite piu_zz_inPn_1024_1012.
    rewrite piu_zz_inPn_1024_1011.
    rewrite piu_zz_inPn_1024_1010.
    rewrite piu_zz_inPn_1024_1009.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb65 : piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) 16%nat = ((if zz_in_Pn 1024 993%nat then Z.of_nat 993%nat else 1%Z) * ((if zz_in_Pn 1024 994%nat then Z.of_nat 994%nat else 1%Z) * ((if zz_in_Pn 1024 995%nat then Z.of_nat 995%nat else 1%Z) * ((if zz_in_Pn 1024 996%nat then Z.of_nat 996%nat else 1%Z) * ((if zz_in_Pn 1024 997%nat then Z.of_nat 997%nat else 1%Z) * ((if zz_in_Pn 1024 998%nat then Z.of_nat 998%nat else 1%Z) * ((if zz_in_Pn 1024 999%nat then Z.of_nat 999%nat else 1%Z) * ((if zz_in_Pn 1024 1000%nat then Z.of_nat 1000%nat else 1%Z) * ((if zz_in_Pn 1024 1001%nat then Z.of_nat 1001%nat else 1%Z) * ((if zz_in_Pn 1024 1002%nat then Z.of_nat 1002%nat else 1%Z) * ((if zz_in_Pn 1024 1003%nat then Z.of_nat 1003%nat else 1%Z) * ((if zz_in_Pn 1024 1004%nat then Z.of_nat 1004%nat else 1%Z) * ((if zz_in_Pn 1024 1005%nat then Z.of_nat 1005%nat else 1%Z) * ((if zz_in_Pn 1024 1006%nat then Z.of_nat 1006%nat else 1%Z) * ((if zz_in_Pn 1024 1007%nat then Z.of_nat 1007%nat else 1%Z) * (if zz_in_Pn 1024 1008%nat then Z.of_nat 1008%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1008.
    rewrite piu_zz_inPn_1024_1007.
    rewrite piu_zz_inPn_1024_1006.
    rewrite piu_zz_inPn_1024_1005.
    rewrite piu_zz_inPn_1024_1004.
    rewrite piu_zz_inPn_1024_1003.
    rewrite piu_zz_inPn_1024_1002.
    rewrite piu_zz_inPn_1024_1001.
    rewrite piu_zz_inPn_1024_1000.
    rewrite piu_zz_inPn_1024_999.
    rewrite piu_zz_inPn_1024_998.
    rewrite piu_zz_inPn_1024_997.
    rewrite piu_zz_inPn_1024_996.
    rewrite piu_zz_inPn_1024_995.
    rewrite piu_zz_inPn_1024_994.
    rewrite piu_zz_inPn_1024_993.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb66 : piu_zz_zprod_seg 1024%nat (512%nat + 464%nat) 16%nat = ((if zz_in_Pn 1024 977%nat then Z.of_nat 977%nat else 1%Z) * ((if zz_in_Pn 1024 978%nat then Z.of_nat 978%nat else 1%Z) * ((if zz_in_Pn 1024 979%nat then Z.of_nat 979%nat else 1%Z) * ((if zz_in_Pn 1024 980%nat then Z.of_nat 980%nat else 1%Z) * ((if zz_in_Pn 1024 981%nat then Z.of_nat 981%nat else 1%Z) * ((if zz_in_Pn 1024 982%nat then Z.of_nat 982%nat else 1%Z) * ((if zz_in_Pn 1024 983%nat then Z.of_nat 983%nat else 1%Z) * ((if zz_in_Pn 1024 984%nat then Z.of_nat 984%nat else 1%Z) * ((if zz_in_Pn 1024 985%nat then Z.of_nat 985%nat else 1%Z) * ((if zz_in_Pn 1024 986%nat then Z.of_nat 986%nat else 1%Z) * ((if zz_in_Pn 1024 987%nat then Z.of_nat 987%nat else 1%Z) * ((if zz_in_Pn 1024 988%nat then Z.of_nat 988%nat else 1%Z) * ((if zz_in_Pn 1024 989%nat then Z.of_nat 989%nat else 1%Z) * ((if zz_in_Pn 1024 990%nat then Z.of_nat 990%nat else 1%Z) * ((if zz_in_Pn 1024 991%nat then Z.of_nat 991%nat else 1%Z) * (if zz_in_Pn 1024 992%nat then Z.of_nat 992%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_992.
    rewrite piu_zz_inPn_1024_991.
    rewrite piu_zz_inPn_1024_990.
    rewrite piu_zz_inPn_1024_989.
    rewrite piu_zz_inPn_1024_988.
    rewrite piu_zz_inPn_1024_987.
    rewrite piu_zz_inPn_1024_986.
    rewrite piu_zz_inPn_1024_985.
    rewrite piu_zz_inPn_1024_984.
    rewrite piu_zz_inPn_1024_983.
    rewrite piu_zz_inPn_1024_982.
    rewrite piu_zz_inPn_1024_981.
    rewrite piu_zz_inPn_1024_980.
    rewrite piu_zz_inPn_1024_979.
    rewrite piu_zz_inPn_1024_978.
    rewrite piu_zz_inPn_1024_977.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb67 : piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 16%nat = ((if zz_in_Pn 1024 961%nat then Z.of_nat 961%nat else 1%Z) * ((if zz_in_Pn 1024 962%nat then Z.of_nat 962%nat else 1%Z) * ((if zz_in_Pn 1024 963%nat then Z.of_nat 963%nat else 1%Z) * ((if zz_in_Pn 1024 964%nat then Z.of_nat 964%nat else 1%Z) * ((if zz_in_Pn 1024 965%nat then Z.of_nat 965%nat else 1%Z) * ((if zz_in_Pn 1024 966%nat then Z.of_nat 966%nat else 1%Z) * ((if zz_in_Pn 1024 967%nat then Z.of_nat 967%nat else 1%Z) * ((if zz_in_Pn 1024 968%nat then Z.of_nat 968%nat else 1%Z) * ((if zz_in_Pn 1024 969%nat then Z.of_nat 969%nat else 1%Z) * ((if zz_in_Pn 1024 970%nat then Z.of_nat 970%nat else 1%Z) * ((if zz_in_Pn 1024 971%nat then Z.of_nat 971%nat else 1%Z) * ((if zz_in_Pn 1024 972%nat then Z.of_nat 972%nat else 1%Z) * ((if zz_in_Pn 1024 973%nat then Z.of_nat 973%nat else 1%Z) * ((if zz_in_Pn 1024 974%nat then Z.of_nat 974%nat else 1%Z) * ((if zz_in_Pn 1024 975%nat then Z.of_nat 975%nat else 1%Z) * (if zz_in_Pn 1024 976%nat then Z.of_nat 976%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_976.
    rewrite piu_zz_inPn_1024_975.
    rewrite piu_zz_inPn_1024_974.
    rewrite piu_zz_inPn_1024_973.
    rewrite piu_zz_inPn_1024_972.
    rewrite piu_zz_inPn_1024_971.
    rewrite piu_zz_inPn_1024_970.
    rewrite piu_zz_inPn_1024_969.
    rewrite piu_zz_inPn_1024_968.
    rewrite piu_zz_inPn_1024_967.
    rewrite piu_zz_inPn_1024_966.
    rewrite piu_zz_inPn_1024_965.
    rewrite piu_zz_inPn_1024_964.
    rewrite piu_zz_inPn_1024_963.
    rewrite piu_zz_inPn_1024_962.
    rewrite piu_zz_inPn_1024_961.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb68 : piu_zz_zprod_seg 1024%nat (512%nat + 432%nat) 16%nat = ((if zz_in_Pn 1024 945%nat then Z.of_nat 945%nat else 1%Z) * ((if zz_in_Pn 1024 946%nat then Z.of_nat 946%nat else 1%Z) * ((if zz_in_Pn 1024 947%nat then Z.of_nat 947%nat else 1%Z) * ((if zz_in_Pn 1024 948%nat then Z.of_nat 948%nat else 1%Z) * ((if zz_in_Pn 1024 949%nat then Z.of_nat 949%nat else 1%Z) * ((if zz_in_Pn 1024 950%nat then Z.of_nat 950%nat else 1%Z) * ((if zz_in_Pn 1024 951%nat then Z.of_nat 951%nat else 1%Z) * ((if zz_in_Pn 1024 952%nat then Z.of_nat 952%nat else 1%Z) * ((if zz_in_Pn 1024 953%nat then Z.of_nat 953%nat else 1%Z) * ((if zz_in_Pn 1024 954%nat then Z.of_nat 954%nat else 1%Z) * ((if zz_in_Pn 1024 955%nat then Z.of_nat 955%nat else 1%Z) * ((if zz_in_Pn 1024 956%nat then Z.of_nat 956%nat else 1%Z) * ((if zz_in_Pn 1024 957%nat then Z.of_nat 957%nat else 1%Z) * ((if zz_in_Pn 1024 958%nat then Z.of_nat 958%nat else 1%Z) * ((if zz_in_Pn 1024 959%nat then Z.of_nat 959%nat else 1%Z) * (if zz_in_Pn 1024 960%nat then Z.of_nat 960%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_960.
    rewrite piu_zz_inPn_1024_959.
    rewrite piu_zz_inPn_1024_958.
    rewrite piu_zz_inPn_1024_957.
    rewrite piu_zz_inPn_1024_956.
    rewrite piu_zz_inPn_1024_955.
    rewrite piu_zz_inPn_1024_954.
    rewrite piu_zz_inPn_1024_953.
    rewrite piu_zz_inPn_1024_952.
    rewrite piu_zz_inPn_1024_951.
    rewrite piu_zz_inPn_1024_950.
    rewrite piu_zz_inPn_1024_949.
    rewrite piu_zz_inPn_1024_948.
    rewrite piu_zz_inPn_1024_947.
    rewrite piu_zz_inPn_1024_946.
    rewrite piu_zz_inPn_1024_945.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb69 : piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) 16%nat = ((if zz_in_Pn 1024 929%nat then Z.of_nat 929%nat else 1%Z) * ((if zz_in_Pn 1024 930%nat then Z.of_nat 930%nat else 1%Z) * ((if zz_in_Pn 1024 931%nat then Z.of_nat 931%nat else 1%Z) * ((if zz_in_Pn 1024 932%nat then Z.of_nat 932%nat else 1%Z) * ((if zz_in_Pn 1024 933%nat then Z.of_nat 933%nat else 1%Z) * ((if zz_in_Pn 1024 934%nat then Z.of_nat 934%nat else 1%Z) * ((if zz_in_Pn 1024 935%nat then Z.of_nat 935%nat else 1%Z) * ((if zz_in_Pn 1024 936%nat then Z.of_nat 936%nat else 1%Z) * ((if zz_in_Pn 1024 937%nat then Z.of_nat 937%nat else 1%Z) * ((if zz_in_Pn 1024 938%nat then Z.of_nat 938%nat else 1%Z) * ((if zz_in_Pn 1024 939%nat then Z.of_nat 939%nat else 1%Z) * ((if zz_in_Pn 1024 940%nat then Z.of_nat 940%nat else 1%Z) * ((if zz_in_Pn 1024 941%nat then Z.of_nat 941%nat else 1%Z) * ((if zz_in_Pn 1024 942%nat then Z.of_nat 942%nat else 1%Z) * ((if zz_in_Pn 1024 943%nat then Z.of_nat 943%nat else 1%Z) * (if zz_in_Pn 1024 944%nat then Z.of_nat 944%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_944.
    rewrite piu_zz_inPn_1024_943.
    rewrite piu_zz_inPn_1024_942.
    rewrite piu_zz_inPn_1024_941.
    rewrite piu_zz_inPn_1024_940.
    rewrite piu_zz_inPn_1024_939.
    rewrite piu_zz_inPn_1024_938.
    rewrite piu_zz_inPn_1024_937.
    rewrite piu_zz_inPn_1024_936.
    rewrite piu_zz_inPn_1024_935.
    rewrite piu_zz_inPn_1024_934.
    rewrite piu_zz_inPn_1024_933.
    rewrite piu_zz_inPn_1024_932.
    rewrite piu_zz_inPn_1024_931.
    rewrite piu_zz_inPn_1024_930.
    rewrite piu_zz_inPn_1024_929.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb70 : piu_zz_zprod_seg 1024%nat (512%nat + 400%nat) 16%nat = ((if zz_in_Pn 1024 913%nat then Z.of_nat 913%nat else 1%Z) * ((if zz_in_Pn 1024 914%nat then Z.of_nat 914%nat else 1%Z) * ((if zz_in_Pn 1024 915%nat then Z.of_nat 915%nat else 1%Z) * ((if zz_in_Pn 1024 916%nat then Z.of_nat 916%nat else 1%Z) * ((if zz_in_Pn 1024 917%nat then Z.of_nat 917%nat else 1%Z) * ((if zz_in_Pn 1024 918%nat then Z.of_nat 918%nat else 1%Z) * ((if zz_in_Pn 1024 919%nat then Z.of_nat 919%nat else 1%Z) * ((if zz_in_Pn 1024 920%nat then Z.of_nat 920%nat else 1%Z) * ((if zz_in_Pn 1024 921%nat then Z.of_nat 921%nat else 1%Z) * ((if zz_in_Pn 1024 922%nat then Z.of_nat 922%nat else 1%Z) * ((if zz_in_Pn 1024 923%nat then Z.of_nat 923%nat else 1%Z) * ((if zz_in_Pn 1024 924%nat then Z.of_nat 924%nat else 1%Z) * ((if zz_in_Pn 1024 925%nat then Z.of_nat 925%nat else 1%Z) * ((if zz_in_Pn 1024 926%nat then Z.of_nat 926%nat else 1%Z) * ((if zz_in_Pn 1024 927%nat then Z.of_nat 927%nat else 1%Z) * (if zz_in_Pn 1024 928%nat then Z.of_nat 928%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_928.
    rewrite piu_zz_inPn_1024_927.
    rewrite piu_zz_inPn_1024_926.
    rewrite piu_zz_inPn_1024_925.
    rewrite piu_zz_inPn_1024_924.
    rewrite piu_zz_inPn_1024_923.
    rewrite piu_zz_inPn_1024_922.
    rewrite piu_zz_inPn_1024_921.
    rewrite piu_zz_inPn_1024_920.
    rewrite piu_zz_inPn_1024_919.
    rewrite piu_zz_inPn_1024_918.
    rewrite piu_zz_inPn_1024_917.
    rewrite piu_zz_inPn_1024_916.
    rewrite piu_zz_inPn_1024_915.
    rewrite piu_zz_inPn_1024_914.
    rewrite piu_zz_inPn_1024_913.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb71 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 16%nat = ((if zz_in_Pn 1024 897%nat then Z.of_nat 897%nat else 1%Z) * ((if zz_in_Pn 1024 898%nat then Z.of_nat 898%nat else 1%Z) * ((if zz_in_Pn 1024 899%nat then Z.of_nat 899%nat else 1%Z) * ((if zz_in_Pn 1024 900%nat then Z.of_nat 900%nat else 1%Z) * ((if zz_in_Pn 1024 901%nat then Z.of_nat 901%nat else 1%Z) * ((if zz_in_Pn 1024 902%nat then Z.of_nat 902%nat else 1%Z) * ((if zz_in_Pn 1024 903%nat then Z.of_nat 903%nat else 1%Z) * ((if zz_in_Pn 1024 904%nat then Z.of_nat 904%nat else 1%Z) * ((if zz_in_Pn 1024 905%nat then Z.of_nat 905%nat else 1%Z) * ((if zz_in_Pn 1024 906%nat then Z.of_nat 906%nat else 1%Z) * ((if zz_in_Pn 1024 907%nat then Z.of_nat 907%nat else 1%Z) * ((if zz_in_Pn 1024 908%nat then Z.of_nat 908%nat else 1%Z) * ((if zz_in_Pn 1024 909%nat then Z.of_nat 909%nat else 1%Z) * ((if zz_in_Pn 1024 910%nat then Z.of_nat 910%nat else 1%Z) * ((if zz_in_Pn 1024 911%nat then Z.of_nat 911%nat else 1%Z) * (if zz_in_Pn 1024 912%nat then Z.of_nat 912%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_912.
    rewrite piu_zz_inPn_1024_911.
    rewrite piu_zz_inPn_1024_910.
    rewrite piu_zz_inPn_1024_909.
    rewrite piu_zz_inPn_1024_908.
    rewrite piu_zz_inPn_1024_907.
    rewrite piu_zz_inPn_1024_906.
    rewrite piu_zz_inPn_1024_905.
    rewrite piu_zz_inPn_1024_904.
    rewrite piu_zz_inPn_1024_903.
    rewrite piu_zz_inPn_1024_902.
    rewrite piu_zz_inPn_1024_901.
    rewrite piu_zz_inPn_1024_900.
    rewrite piu_zz_inPn_1024_899.
    rewrite piu_zz_inPn_1024_898.
    rewrite piu_zz_inPn_1024_897.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb72 : piu_zz_zprod_seg 1024%nat (512%nat + 368%nat) 16%nat = ((if zz_in_Pn 1024 881%nat then Z.of_nat 881%nat else 1%Z) * ((if zz_in_Pn 1024 882%nat then Z.of_nat 882%nat else 1%Z) * ((if zz_in_Pn 1024 883%nat then Z.of_nat 883%nat else 1%Z) * ((if zz_in_Pn 1024 884%nat then Z.of_nat 884%nat else 1%Z) * ((if zz_in_Pn 1024 885%nat then Z.of_nat 885%nat else 1%Z) * ((if zz_in_Pn 1024 886%nat then Z.of_nat 886%nat else 1%Z) * ((if zz_in_Pn 1024 887%nat then Z.of_nat 887%nat else 1%Z) * ((if zz_in_Pn 1024 888%nat then Z.of_nat 888%nat else 1%Z) * ((if zz_in_Pn 1024 889%nat then Z.of_nat 889%nat else 1%Z) * ((if zz_in_Pn 1024 890%nat then Z.of_nat 890%nat else 1%Z) * ((if zz_in_Pn 1024 891%nat then Z.of_nat 891%nat else 1%Z) * ((if zz_in_Pn 1024 892%nat then Z.of_nat 892%nat else 1%Z) * ((if zz_in_Pn 1024 893%nat then Z.of_nat 893%nat else 1%Z) * ((if zz_in_Pn 1024 894%nat then Z.of_nat 894%nat else 1%Z) * ((if zz_in_Pn 1024 895%nat then Z.of_nat 895%nat else 1%Z) * (if zz_in_Pn 1024 896%nat then Z.of_nat 896%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_896.
    rewrite piu_zz_inPn_1024_895.
    rewrite piu_zz_inPn_1024_894.
    rewrite piu_zz_inPn_1024_893.
    rewrite piu_zz_inPn_1024_892.
    rewrite piu_zz_inPn_1024_891.
    rewrite piu_zz_inPn_1024_890.
    rewrite piu_zz_inPn_1024_889.
    rewrite piu_zz_inPn_1024_888.
    rewrite piu_zz_inPn_1024_887.
    rewrite piu_zz_inPn_1024_886.
    rewrite piu_zz_inPn_1024_885.
    rewrite piu_zz_inPn_1024_884.
    rewrite piu_zz_inPn_1024_883.
    rewrite piu_zz_inPn_1024_882.
    rewrite piu_zz_inPn_1024_881.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb73 : piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) 16%nat = ((if zz_in_Pn 1024 865%nat then Z.of_nat 865%nat else 1%Z) * ((if zz_in_Pn 1024 866%nat then Z.of_nat 866%nat else 1%Z) * ((if zz_in_Pn 1024 867%nat then Z.of_nat 867%nat else 1%Z) * ((if zz_in_Pn 1024 868%nat then Z.of_nat 868%nat else 1%Z) * ((if zz_in_Pn 1024 869%nat then Z.of_nat 869%nat else 1%Z) * ((if zz_in_Pn 1024 870%nat then Z.of_nat 870%nat else 1%Z) * ((if zz_in_Pn 1024 871%nat then Z.of_nat 871%nat else 1%Z) * ((if zz_in_Pn 1024 872%nat then Z.of_nat 872%nat else 1%Z) * ((if zz_in_Pn 1024 873%nat then Z.of_nat 873%nat else 1%Z) * ((if zz_in_Pn 1024 874%nat then Z.of_nat 874%nat else 1%Z) * ((if zz_in_Pn 1024 875%nat then Z.of_nat 875%nat else 1%Z) * ((if zz_in_Pn 1024 876%nat then Z.of_nat 876%nat else 1%Z) * ((if zz_in_Pn 1024 877%nat then Z.of_nat 877%nat else 1%Z) * ((if zz_in_Pn 1024 878%nat then Z.of_nat 878%nat else 1%Z) * ((if zz_in_Pn 1024 879%nat then Z.of_nat 879%nat else 1%Z) * (if zz_in_Pn 1024 880%nat then Z.of_nat 880%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_880.
    rewrite piu_zz_inPn_1024_879.
    rewrite piu_zz_inPn_1024_878.
    rewrite piu_zz_inPn_1024_877.
    rewrite piu_zz_inPn_1024_876.
    rewrite piu_zz_inPn_1024_875.
    rewrite piu_zz_inPn_1024_874.
    rewrite piu_zz_inPn_1024_873.
    rewrite piu_zz_inPn_1024_872.
    rewrite piu_zz_inPn_1024_871.
    rewrite piu_zz_inPn_1024_870.
    rewrite piu_zz_inPn_1024_869.
    rewrite piu_zz_inPn_1024_868.
    rewrite piu_zz_inPn_1024_867.
    rewrite piu_zz_inPn_1024_866.
    rewrite piu_zz_inPn_1024_865.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb74 : piu_zz_zprod_seg 1024%nat (512%nat + 336%nat) 16%nat = ((if zz_in_Pn 1024 849%nat then Z.of_nat 849%nat else 1%Z) * ((if zz_in_Pn 1024 850%nat then Z.of_nat 850%nat else 1%Z) * ((if zz_in_Pn 1024 851%nat then Z.of_nat 851%nat else 1%Z) * ((if zz_in_Pn 1024 852%nat then Z.of_nat 852%nat else 1%Z) * ((if zz_in_Pn 1024 853%nat then Z.of_nat 853%nat else 1%Z) * ((if zz_in_Pn 1024 854%nat then Z.of_nat 854%nat else 1%Z) * ((if zz_in_Pn 1024 855%nat then Z.of_nat 855%nat else 1%Z) * ((if zz_in_Pn 1024 856%nat then Z.of_nat 856%nat else 1%Z) * ((if zz_in_Pn 1024 857%nat then Z.of_nat 857%nat else 1%Z) * ((if zz_in_Pn 1024 858%nat then Z.of_nat 858%nat else 1%Z) * ((if zz_in_Pn 1024 859%nat then Z.of_nat 859%nat else 1%Z) * ((if zz_in_Pn 1024 860%nat then Z.of_nat 860%nat else 1%Z) * ((if zz_in_Pn 1024 861%nat then Z.of_nat 861%nat else 1%Z) * ((if zz_in_Pn 1024 862%nat then Z.of_nat 862%nat else 1%Z) * ((if zz_in_Pn 1024 863%nat then Z.of_nat 863%nat else 1%Z) * (if zz_in_Pn 1024 864%nat then Z.of_nat 864%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_864.
    rewrite piu_zz_inPn_1024_863.
    rewrite piu_zz_inPn_1024_862.
    rewrite piu_zz_inPn_1024_861.
    rewrite piu_zz_inPn_1024_860.
    rewrite piu_zz_inPn_1024_859.
    rewrite piu_zz_inPn_1024_858.
    rewrite piu_zz_inPn_1024_857.
    rewrite piu_zz_inPn_1024_856.
    rewrite piu_zz_inPn_1024_855.
    rewrite piu_zz_inPn_1024_854.
    rewrite piu_zz_inPn_1024_853.
    rewrite piu_zz_inPn_1024_852.
    rewrite piu_zz_inPn_1024_851.
    rewrite piu_zz_inPn_1024_850.
    rewrite piu_zz_inPn_1024_849.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb75 : piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 16%nat = ((if zz_in_Pn 1024 833%nat then Z.of_nat 833%nat else 1%Z) * ((if zz_in_Pn 1024 834%nat then Z.of_nat 834%nat else 1%Z) * ((if zz_in_Pn 1024 835%nat then Z.of_nat 835%nat else 1%Z) * ((if zz_in_Pn 1024 836%nat then Z.of_nat 836%nat else 1%Z) * ((if zz_in_Pn 1024 837%nat then Z.of_nat 837%nat else 1%Z) * ((if zz_in_Pn 1024 838%nat then Z.of_nat 838%nat else 1%Z) * ((if zz_in_Pn 1024 839%nat then Z.of_nat 839%nat else 1%Z) * ((if zz_in_Pn 1024 840%nat then Z.of_nat 840%nat else 1%Z) * ((if zz_in_Pn 1024 841%nat then Z.of_nat 841%nat else 1%Z) * ((if zz_in_Pn 1024 842%nat then Z.of_nat 842%nat else 1%Z) * ((if zz_in_Pn 1024 843%nat then Z.of_nat 843%nat else 1%Z) * ((if zz_in_Pn 1024 844%nat then Z.of_nat 844%nat else 1%Z) * ((if zz_in_Pn 1024 845%nat then Z.of_nat 845%nat else 1%Z) * ((if zz_in_Pn 1024 846%nat then Z.of_nat 846%nat else 1%Z) * ((if zz_in_Pn 1024 847%nat then Z.of_nat 847%nat else 1%Z) * (if zz_in_Pn 1024 848%nat then Z.of_nat 848%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_848.
    rewrite piu_zz_inPn_1024_847.
    rewrite piu_zz_inPn_1024_846.
    rewrite piu_zz_inPn_1024_845.
    rewrite piu_zz_inPn_1024_844.
    rewrite piu_zz_inPn_1024_843.
    rewrite piu_zz_inPn_1024_842.
    rewrite piu_zz_inPn_1024_841.
    rewrite piu_zz_inPn_1024_840.
    rewrite piu_zz_inPn_1024_839.
    rewrite piu_zz_inPn_1024_838.
    rewrite piu_zz_inPn_1024_837.
    rewrite piu_zz_inPn_1024_836.
    rewrite piu_zz_inPn_1024_835.
    rewrite piu_zz_inPn_1024_834.
    rewrite piu_zz_inPn_1024_833.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb76 : piu_zz_zprod_seg 1024%nat (512%nat + 304%nat) 16%nat = ((if zz_in_Pn 1024 817%nat then Z.of_nat 817%nat else 1%Z) * ((if zz_in_Pn 1024 818%nat then Z.of_nat 818%nat else 1%Z) * ((if zz_in_Pn 1024 819%nat then Z.of_nat 819%nat else 1%Z) * ((if zz_in_Pn 1024 820%nat then Z.of_nat 820%nat else 1%Z) * ((if zz_in_Pn 1024 821%nat then Z.of_nat 821%nat else 1%Z) * ((if zz_in_Pn 1024 822%nat then Z.of_nat 822%nat else 1%Z) * ((if zz_in_Pn 1024 823%nat then Z.of_nat 823%nat else 1%Z) * ((if zz_in_Pn 1024 824%nat then Z.of_nat 824%nat else 1%Z) * ((if zz_in_Pn 1024 825%nat then Z.of_nat 825%nat else 1%Z) * ((if zz_in_Pn 1024 826%nat then Z.of_nat 826%nat else 1%Z) * ((if zz_in_Pn 1024 827%nat then Z.of_nat 827%nat else 1%Z) * ((if zz_in_Pn 1024 828%nat then Z.of_nat 828%nat else 1%Z) * ((if zz_in_Pn 1024 829%nat then Z.of_nat 829%nat else 1%Z) * ((if zz_in_Pn 1024 830%nat then Z.of_nat 830%nat else 1%Z) * ((if zz_in_Pn 1024 831%nat then Z.of_nat 831%nat else 1%Z) * (if zz_in_Pn 1024 832%nat then Z.of_nat 832%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_832.
    rewrite piu_zz_inPn_1024_831.
    rewrite piu_zz_inPn_1024_830.
    rewrite piu_zz_inPn_1024_829.
    rewrite piu_zz_inPn_1024_828.
    rewrite piu_zz_inPn_1024_827.
    rewrite piu_zz_inPn_1024_826.
    rewrite piu_zz_inPn_1024_825.
    rewrite piu_zz_inPn_1024_824.
    rewrite piu_zz_inPn_1024_823.
    rewrite piu_zz_inPn_1024_822.
    rewrite piu_zz_inPn_1024_821.
    rewrite piu_zz_inPn_1024_820.
    rewrite piu_zz_inPn_1024_819.
    rewrite piu_zz_inPn_1024_818.
    rewrite piu_zz_inPn_1024_817.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb77 : piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) 16%nat = ((if zz_in_Pn 1024 801%nat then Z.of_nat 801%nat else 1%Z) * ((if zz_in_Pn 1024 802%nat then Z.of_nat 802%nat else 1%Z) * ((if zz_in_Pn 1024 803%nat then Z.of_nat 803%nat else 1%Z) * ((if zz_in_Pn 1024 804%nat then Z.of_nat 804%nat else 1%Z) * ((if zz_in_Pn 1024 805%nat then Z.of_nat 805%nat else 1%Z) * ((if zz_in_Pn 1024 806%nat then Z.of_nat 806%nat else 1%Z) * ((if zz_in_Pn 1024 807%nat then Z.of_nat 807%nat else 1%Z) * ((if zz_in_Pn 1024 808%nat then Z.of_nat 808%nat else 1%Z) * ((if zz_in_Pn 1024 809%nat then Z.of_nat 809%nat else 1%Z) * ((if zz_in_Pn 1024 810%nat then Z.of_nat 810%nat else 1%Z) * ((if zz_in_Pn 1024 811%nat then Z.of_nat 811%nat else 1%Z) * ((if zz_in_Pn 1024 812%nat then Z.of_nat 812%nat else 1%Z) * ((if zz_in_Pn 1024 813%nat then Z.of_nat 813%nat else 1%Z) * ((if zz_in_Pn 1024 814%nat then Z.of_nat 814%nat else 1%Z) * ((if zz_in_Pn 1024 815%nat then Z.of_nat 815%nat else 1%Z) * (if zz_in_Pn 1024 816%nat then Z.of_nat 816%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_816.
    rewrite piu_zz_inPn_1024_815.
    rewrite piu_zz_inPn_1024_814.
    rewrite piu_zz_inPn_1024_813.
    rewrite piu_zz_inPn_1024_812.
    rewrite piu_zz_inPn_1024_811.
    rewrite piu_zz_inPn_1024_810.
    rewrite piu_zz_inPn_1024_809.
    rewrite piu_zz_inPn_1024_808.
    rewrite piu_zz_inPn_1024_807.
    rewrite piu_zz_inPn_1024_806.
    rewrite piu_zz_inPn_1024_805.
    rewrite piu_zz_inPn_1024_804.
    rewrite piu_zz_inPn_1024_803.
    rewrite piu_zz_inPn_1024_802.
    rewrite piu_zz_inPn_1024_801.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb78 : piu_zz_zprod_seg 1024%nat (512%nat + 272%nat) 16%nat = ((if zz_in_Pn 1024 785%nat then Z.of_nat 785%nat else 1%Z) * ((if zz_in_Pn 1024 786%nat then Z.of_nat 786%nat else 1%Z) * ((if zz_in_Pn 1024 787%nat then Z.of_nat 787%nat else 1%Z) * ((if zz_in_Pn 1024 788%nat then Z.of_nat 788%nat else 1%Z) * ((if zz_in_Pn 1024 789%nat then Z.of_nat 789%nat else 1%Z) * ((if zz_in_Pn 1024 790%nat then Z.of_nat 790%nat else 1%Z) * ((if zz_in_Pn 1024 791%nat then Z.of_nat 791%nat else 1%Z) * ((if zz_in_Pn 1024 792%nat then Z.of_nat 792%nat else 1%Z) * ((if zz_in_Pn 1024 793%nat then Z.of_nat 793%nat else 1%Z) * ((if zz_in_Pn 1024 794%nat then Z.of_nat 794%nat else 1%Z) * ((if zz_in_Pn 1024 795%nat then Z.of_nat 795%nat else 1%Z) * ((if zz_in_Pn 1024 796%nat then Z.of_nat 796%nat else 1%Z) * ((if zz_in_Pn 1024 797%nat then Z.of_nat 797%nat else 1%Z) * ((if zz_in_Pn 1024 798%nat then Z.of_nat 798%nat else 1%Z) * ((if zz_in_Pn 1024 799%nat then Z.of_nat 799%nat else 1%Z) * (if zz_in_Pn 1024 800%nat then Z.of_nat 800%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_800.
    rewrite piu_zz_inPn_1024_799.
    rewrite piu_zz_inPn_1024_798.
    rewrite piu_zz_inPn_1024_797.
    rewrite piu_zz_inPn_1024_796.
    rewrite piu_zz_inPn_1024_795.
    rewrite piu_zz_inPn_1024_794.
    rewrite piu_zz_inPn_1024_793.
    rewrite piu_zz_inPn_1024_792.
    rewrite piu_zz_inPn_1024_791.
    rewrite piu_zz_inPn_1024_790.
    rewrite piu_zz_inPn_1024_789.
    rewrite piu_zz_inPn_1024_788.
    rewrite piu_zz_inPn_1024_787.
    rewrite piu_zz_inPn_1024_786.
    rewrite piu_zz_inPn_1024_785.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb79 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 16%nat = ((if zz_in_Pn 1024 769%nat then Z.of_nat 769%nat else 1%Z) * ((if zz_in_Pn 1024 770%nat then Z.of_nat 770%nat else 1%Z) * ((if zz_in_Pn 1024 771%nat then Z.of_nat 771%nat else 1%Z) * ((if zz_in_Pn 1024 772%nat then Z.of_nat 772%nat else 1%Z) * ((if zz_in_Pn 1024 773%nat then Z.of_nat 773%nat else 1%Z) * ((if zz_in_Pn 1024 774%nat then Z.of_nat 774%nat else 1%Z) * ((if zz_in_Pn 1024 775%nat then Z.of_nat 775%nat else 1%Z) * ((if zz_in_Pn 1024 776%nat then Z.of_nat 776%nat else 1%Z) * ((if zz_in_Pn 1024 777%nat then Z.of_nat 777%nat else 1%Z) * ((if zz_in_Pn 1024 778%nat then Z.of_nat 778%nat else 1%Z) * ((if zz_in_Pn 1024 779%nat then Z.of_nat 779%nat else 1%Z) * ((if zz_in_Pn 1024 780%nat then Z.of_nat 780%nat else 1%Z) * ((if zz_in_Pn 1024 781%nat then Z.of_nat 781%nat else 1%Z) * ((if zz_in_Pn 1024 782%nat then Z.of_nat 782%nat else 1%Z) * ((if zz_in_Pn 1024 783%nat then Z.of_nat 783%nat else 1%Z) * (if zz_in_Pn 1024 784%nat then Z.of_nat 784%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_784.
    rewrite piu_zz_inPn_1024_783.
    rewrite piu_zz_inPn_1024_782.
    rewrite piu_zz_inPn_1024_781.
    rewrite piu_zz_inPn_1024_780.
    rewrite piu_zz_inPn_1024_779.
    rewrite piu_zz_inPn_1024_778.
    rewrite piu_zz_inPn_1024_777.
    rewrite piu_zz_inPn_1024_776.
    rewrite piu_zz_inPn_1024_775.
    rewrite piu_zz_inPn_1024_774.
    rewrite piu_zz_inPn_1024_773.
    rewrite piu_zz_inPn_1024_772.
    rewrite piu_zz_inPn_1024_771.
    rewrite piu_zz_inPn_1024_770.
    rewrite piu_zz_inPn_1024_769.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb80 : piu_zz_zprod_seg 1024%nat (512%nat + 240%nat) 16%nat = ((if zz_in_Pn 1024 753%nat then Z.of_nat 753%nat else 1%Z) * ((if zz_in_Pn 1024 754%nat then Z.of_nat 754%nat else 1%Z) * ((if zz_in_Pn 1024 755%nat then Z.of_nat 755%nat else 1%Z) * ((if zz_in_Pn 1024 756%nat then Z.of_nat 756%nat else 1%Z) * ((if zz_in_Pn 1024 757%nat then Z.of_nat 757%nat else 1%Z) * ((if zz_in_Pn 1024 758%nat then Z.of_nat 758%nat else 1%Z) * ((if zz_in_Pn 1024 759%nat then Z.of_nat 759%nat else 1%Z) * ((if zz_in_Pn 1024 760%nat then Z.of_nat 760%nat else 1%Z) * ((if zz_in_Pn 1024 761%nat then Z.of_nat 761%nat else 1%Z) * ((if zz_in_Pn 1024 762%nat then Z.of_nat 762%nat else 1%Z) * ((if zz_in_Pn 1024 763%nat then Z.of_nat 763%nat else 1%Z) * ((if zz_in_Pn 1024 764%nat then Z.of_nat 764%nat else 1%Z) * ((if zz_in_Pn 1024 765%nat then Z.of_nat 765%nat else 1%Z) * ((if zz_in_Pn 1024 766%nat then Z.of_nat 766%nat else 1%Z) * ((if zz_in_Pn 1024 767%nat then Z.of_nat 767%nat else 1%Z) * (if zz_in_Pn 1024 768%nat then Z.of_nat 768%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_768.
    rewrite piu_zz_inPn_1024_767.
    rewrite piu_zz_inPn_1024_766.
    rewrite piu_zz_inPn_1024_765.
    rewrite piu_zz_inPn_1024_764.
    rewrite piu_zz_inPn_1024_763.
    rewrite piu_zz_inPn_1024_762.
    rewrite piu_zz_inPn_1024_761.
    rewrite piu_zz_inPn_1024_760.
    rewrite piu_zz_inPn_1024_759.
    rewrite piu_zz_inPn_1024_758.
    rewrite piu_zz_inPn_1024_757.
    rewrite piu_zz_inPn_1024_756.
    rewrite piu_zz_inPn_1024_755.
    rewrite piu_zz_inPn_1024_754.
    rewrite piu_zz_inPn_1024_753.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb81 : piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) 16%nat = ((if zz_in_Pn 1024 737%nat then Z.of_nat 737%nat else 1%Z) * ((if zz_in_Pn 1024 738%nat then Z.of_nat 738%nat else 1%Z) * ((if zz_in_Pn 1024 739%nat then Z.of_nat 739%nat else 1%Z) * ((if zz_in_Pn 1024 740%nat then Z.of_nat 740%nat else 1%Z) * ((if zz_in_Pn 1024 741%nat then Z.of_nat 741%nat else 1%Z) * ((if zz_in_Pn 1024 742%nat then Z.of_nat 742%nat else 1%Z) * ((if zz_in_Pn 1024 743%nat then Z.of_nat 743%nat else 1%Z) * ((if zz_in_Pn 1024 744%nat then Z.of_nat 744%nat else 1%Z) * ((if zz_in_Pn 1024 745%nat then Z.of_nat 745%nat else 1%Z) * ((if zz_in_Pn 1024 746%nat then Z.of_nat 746%nat else 1%Z) * ((if zz_in_Pn 1024 747%nat then Z.of_nat 747%nat else 1%Z) * ((if zz_in_Pn 1024 748%nat then Z.of_nat 748%nat else 1%Z) * ((if zz_in_Pn 1024 749%nat then Z.of_nat 749%nat else 1%Z) * ((if zz_in_Pn 1024 750%nat then Z.of_nat 750%nat else 1%Z) * ((if zz_in_Pn 1024 751%nat then Z.of_nat 751%nat else 1%Z) * (if zz_in_Pn 1024 752%nat then Z.of_nat 752%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_752.
    rewrite piu_zz_inPn_1024_751.
    rewrite piu_zz_inPn_1024_750.
    rewrite piu_zz_inPn_1024_749.
    rewrite piu_zz_inPn_1024_748.
    rewrite piu_zz_inPn_1024_747.
    rewrite piu_zz_inPn_1024_746.
    rewrite piu_zz_inPn_1024_745.
    rewrite piu_zz_inPn_1024_744.
    rewrite piu_zz_inPn_1024_743.
    rewrite piu_zz_inPn_1024_742.
    rewrite piu_zz_inPn_1024_741.
    rewrite piu_zz_inPn_1024_740.
    rewrite piu_zz_inPn_1024_739.
    rewrite piu_zz_inPn_1024_738.
    rewrite piu_zz_inPn_1024_737.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb82 : piu_zz_zprod_seg 1024%nat (512%nat + 208%nat) 16%nat = ((if zz_in_Pn 1024 721%nat then Z.of_nat 721%nat else 1%Z) * ((if zz_in_Pn 1024 722%nat then Z.of_nat 722%nat else 1%Z) * ((if zz_in_Pn 1024 723%nat then Z.of_nat 723%nat else 1%Z) * ((if zz_in_Pn 1024 724%nat then Z.of_nat 724%nat else 1%Z) * ((if zz_in_Pn 1024 725%nat then Z.of_nat 725%nat else 1%Z) * ((if zz_in_Pn 1024 726%nat then Z.of_nat 726%nat else 1%Z) * ((if zz_in_Pn 1024 727%nat then Z.of_nat 727%nat else 1%Z) * ((if zz_in_Pn 1024 728%nat then Z.of_nat 728%nat else 1%Z) * ((if zz_in_Pn 1024 729%nat then Z.of_nat 729%nat else 1%Z) * ((if zz_in_Pn 1024 730%nat then Z.of_nat 730%nat else 1%Z) * ((if zz_in_Pn 1024 731%nat then Z.of_nat 731%nat else 1%Z) * ((if zz_in_Pn 1024 732%nat then Z.of_nat 732%nat else 1%Z) * ((if zz_in_Pn 1024 733%nat then Z.of_nat 733%nat else 1%Z) * ((if zz_in_Pn 1024 734%nat then Z.of_nat 734%nat else 1%Z) * ((if zz_in_Pn 1024 735%nat then Z.of_nat 735%nat else 1%Z) * (if zz_in_Pn 1024 736%nat then Z.of_nat 736%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_736.
    rewrite piu_zz_inPn_1024_735.
    rewrite piu_zz_inPn_1024_734.
    rewrite piu_zz_inPn_1024_733.
    rewrite piu_zz_inPn_1024_732.
    rewrite piu_zz_inPn_1024_731.
    rewrite piu_zz_inPn_1024_730.
    rewrite piu_zz_inPn_1024_729.
    rewrite piu_zz_inPn_1024_728.
    rewrite piu_zz_inPn_1024_727.
    rewrite piu_zz_inPn_1024_726.
    rewrite piu_zz_inPn_1024_725.
    rewrite piu_zz_inPn_1024_724.
    rewrite piu_zz_inPn_1024_723.
    rewrite piu_zz_inPn_1024_722.
    rewrite piu_zz_inPn_1024_721.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb83 : piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 16%nat = ((if zz_in_Pn 1024 705%nat then Z.of_nat 705%nat else 1%Z) * ((if zz_in_Pn 1024 706%nat then Z.of_nat 706%nat else 1%Z) * ((if zz_in_Pn 1024 707%nat then Z.of_nat 707%nat else 1%Z) * ((if zz_in_Pn 1024 708%nat then Z.of_nat 708%nat else 1%Z) * ((if zz_in_Pn 1024 709%nat then Z.of_nat 709%nat else 1%Z) * ((if zz_in_Pn 1024 710%nat then Z.of_nat 710%nat else 1%Z) * ((if zz_in_Pn 1024 711%nat then Z.of_nat 711%nat else 1%Z) * ((if zz_in_Pn 1024 712%nat then Z.of_nat 712%nat else 1%Z) * ((if zz_in_Pn 1024 713%nat then Z.of_nat 713%nat else 1%Z) * ((if zz_in_Pn 1024 714%nat then Z.of_nat 714%nat else 1%Z) * ((if zz_in_Pn 1024 715%nat then Z.of_nat 715%nat else 1%Z) * ((if zz_in_Pn 1024 716%nat then Z.of_nat 716%nat else 1%Z) * ((if zz_in_Pn 1024 717%nat then Z.of_nat 717%nat else 1%Z) * ((if zz_in_Pn 1024 718%nat then Z.of_nat 718%nat else 1%Z) * ((if zz_in_Pn 1024 719%nat then Z.of_nat 719%nat else 1%Z) * (if zz_in_Pn 1024 720%nat then Z.of_nat 720%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_720.
    rewrite piu_zz_inPn_1024_719.
    rewrite piu_zz_inPn_1024_718.
    rewrite piu_zz_inPn_1024_717.
    rewrite piu_zz_inPn_1024_716.
    rewrite piu_zz_inPn_1024_715.
    rewrite piu_zz_inPn_1024_714.
    rewrite piu_zz_inPn_1024_713.
    rewrite piu_zz_inPn_1024_712.
    rewrite piu_zz_inPn_1024_711.
    rewrite piu_zz_inPn_1024_710.
    rewrite piu_zz_inPn_1024_709.
    rewrite piu_zz_inPn_1024_708.
    rewrite piu_zz_inPn_1024_707.
    rewrite piu_zz_inPn_1024_706.
    rewrite piu_zz_inPn_1024_705.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb84 : piu_zz_zprod_seg 1024%nat (512%nat + 176%nat) 16%nat = ((if zz_in_Pn 1024 689%nat then Z.of_nat 689%nat else 1%Z) * ((if zz_in_Pn 1024 690%nat then Z.of_nat 690%nat else 1%Z) * ((if zz_in_Pn 1024 691%nat then Z.of_nat 691%nat else 1%Z) * ((if zz_in_Pn 1024 692%nat then Z.of_nat 692%nat else 1%Z) * ((if zz_in_Pn 1024 693%nat then Z.of_nat 693%nat else 1%Z) * ((if zz_in_Pn 1024 694%nat then Z.of_nat 694%nat else 1%Z) * ((if zz_in_Pn 1024 695%nat then Z.of_nat 695%nat else 1%Z) * ((if zz_in_Pn 1024 696%nat then Z.of_nat 696%nat else 1%Z) * ((if zz_in_Pn 1024 697%nat then Z.of_nat 697%nat else 1%Z) * ((if zz_in_Pn 1024 698%nat then Z.of_nat 698%nat else 1%Z) * ((if zz_in_Pn 1024 699%nat then Z.of_nat 699%nat else 1%Z) * ((if zz_in_Pn 1024 700%nat then Z.of_nat 700%nat else 1%Z) * ((if zz_in_Pn 1024 701%nat then Z.of_nat 701%nat else 1%Z) * ((if zz_in_Pn 1024 702%nat then Z.of_nat 702%nat else 1%Z) * ((if zz_in_Pn 1024 703%nat then Z.of_nat 703%nat else 1%Z) * (if zz_in_Pn 1024 704%nat then Z.of_nat 704%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_704.
    rewrite piu_zz_inPn_1024_703.
    rewrite piu_zz_inPn_1024_702.
    rewrite piu_zz_inPn_1024_701.
    rewrite piu_zz_inPn_1024_700.
    rewrite piu_zz_inPn_1024_699.
    rewrite piu_zz_inPn_1024_698.
    rewrite piu_zz_inPn_1024_697.
    rewrite piu_zz_inPn_1024_696.
    rewrite piu_zz_inPn_1024_695.
    rewrite piu_zz_inPn_1024_694.
    rewrite piu_zz_inPn_1024_693.
    rewrite piu_zz_inPn_1024_692.
    rewrite piu_zz_inPn_1024_691.
    rewrite piu_zz_inPn_1024_690.
    rewrite piu_zz_inPn_1024_689.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb85 : piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) 16%nat = ((if zz_in_Pn 1024 673%nat then Z.of_nat 673%nat else 1%Z) * ((if zz_in_Pn 1024 674%nat then Z.of_nat 674%nat else 1%Z) * ((if zz_in_Pn 1024 675%nat then Z.of_nat 675%nat else 1%Z) * ((if zz_in_Pn 1024 676%nat then Z.of_nat 676%nat else 1%Z) * ((if zz_in_Pn 1024 677%nat then Z.of_nat 677%nat else 1%Z) * ((if zz_in_Pn 1024 678%nat then Z.of_nat 678%nat else 1%Z) * ((if zz_in_Pn 1024 679%nat then Z.of_nat 679%nat else 1%Z) * ((if zz_in_Pn 1024 680%nat then Z.of_nat 680%nat else 1%Z) * ((if zz_in_Pn 1024 681%nat then Z.of_nat 681%nat else 1%Z) * ((if zz_in_Pn 1024 682%nat then Z.of_nat 682%nat else 1%Z) * ((if zz_in_Pn 1024 683%nat then Z.of_nat 683%nat else 1%Z) * ((if zz_in_Pn 1024 684%nat then Z.of_nat 684%nat else 1%Z) * ((if zz_in_Pn 1024 685%nat then Z.of_nat 685%nat else 1%Z) * ((if zz_in_Pn 1024 686%nat then Z.of_nat 686%nat else 1%Z) * ((if zz_in_Pn 1024 687%nat then Z.of_nat 687%nat else 1%Z) * (if zz_in_Pn 1024 688%nat then Z.of_nat 688%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_688.
    rewrite piu_zz_inPn_1024_687.
    rewrite piu_zz_inPn_1024_686.
    rewrite piu_zz_inPn_1024_685.
    rewrite piu_zz_inPn_1024_684.
    rewrite piu_zz_inPn_1024_683.
    rewrite piu_zz_inPn_1024_682.
    rewrite piu_zz_inPn_1024_681.
    rewrite piu_zz_inPn_1024_680.
    rewrite piu_zz_inPn_1024_679.
    rewrite piu_zz_inPn_1024_678.
    rewrite piu_zz_inPn_1024_677.
    rewrite piu_zz_inPn_1024_676.
    rewrite piu_zz_inPn_1024_675.
    rewrite piu_zz_inPn_1024_674.
    rewrite piu_zz_inPn_1024_673.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb86 : piu_zz_zprod_seg 1024%nat (512%nat + 144%nat) 16%nat = ((if zz_in_Pn 1024 657%nat then Z.of_nat 657%nat else 1%Z) * ((if zz_in_Pn 1024 658%nat then Z.of_nat 658%nat else 1%Z) * ((if zz_in_Pn 1024 659%nat then Z.of_nat 659%nat else 1%Z) * ((if zz_in_Pn 1024 660%nat then Z.of_nat 660%nat else 1%Z) * ((if zz_in_Pn 1024 661%nat then Z.of_nat 661%nat else 1%Z) * ((if zz_in_Pn 1024 662%nat then Z.of_nat 662%nat else 1%Z) * ((if zz_in_Pn 1024 663%nat then Z.of_nat 663%nat else 1%Z) * ((if zz_in_Pn 1024 664%nat then Z.of_nat 664%nat else 1%Z) * ((if zz_in_Pn 1024 665%nat then Z.of_nat 665%nat else 1%Z) * ((if zz_in_Pn 1024 666%nat then Z.of_nat 666%nat else 1%Z) * ((if zz_in_Pn 1024 667%nat then Z.of_nat 667%nat else 1%Z) * ((if zz_in_Pn 1024 668%nat then Z.of_nat 668%nat else 1%Z) * ((if zz_in_Pn 1024 669%nat then Z.of_nat 669%nat else 1%Z) * ((if zz_in_Pn 1024 670%nat then Z.of_nat 670%nat else 1%Z) * ((if zz_in_Pn 1024 671%nat then Z.of_nat 671%nat else 1%Z) * (if zz_in_Pn 1024 672%nat then Z.of_nat 672%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_672.
    rewrite piu_zz_inPn_1024_671.
    rewrite piu_zz_inPn_1024_670.
    rewrite piu_zz_inPn_1024_669.
    rewrite piu_zz_inPn_1024_668.
    rewrite piu_zz_inPn_1024_667.
    rewrite piu_zz_inPn_1024_666.
    rewrite piu_zz_inPn_1024_665.
    rewrite piu_zz_inPn_1024_664.
    rewrite piu_zz_inPn_1024_663.
    rewrite piu_zz_inPn_1024_662.
    rewrite piu_zz_inPn_1024_661.
    rewrite piu_zz_inPn_1024_660.
    rewrite piu_zz_inPn_1024_659.
    rewrite piu_zz_inPn_1024_658.
    rewrite piu_zz_inPn_1024_657.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb87 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 16%nat = ((if zz_in_Pn 1024 641%nat then Z.of_nat 641%nat else 1%Z) * ((if zz_in_Pn 1024 642%nat then Z.of_nat 642%nat else 1%Z) * ((if zz_in_Pn 1024 643%nat then Z.of_nat 643%nat else 1%Z) * ((if zz_in_Pn 1024 644%nat then Z.of_nat 644%nat else 1%Z) * ((if zz_in_Pn 1024 645%nat then Z.of_nat 645%nat else 1%Z) * ((if zz_in_Pn 1024 646%nat then Z.of_nat 646%nat else 1%Z) * ((if zz_in_Pn 1024 647%nat then Z.of_nat 647%nat else 1%Z) * ((if zz_in_Pn 1024 648%nat then Z.of_nat 648%nat else 1%Z) * ((if zz_in_Pn 1024 649%nat then Z.of_nat 649%nat else 1%Z) * ((if zz_in_Pn 1024 650%nat then Z.of_nat 650%nat else 1%Z) * ((if zz_in_Pn 1024 651%nat then Z.of_nat 651%nat else 1%Z) * ((if zz_in_Pn 1024 652%nat then Z.of_nat 652%nat else 1%Z) * ((if zz_in_Pn 1024 653%nat then Z.of_nat 653%nat else 1%Z) * ((if zz_in_Pn 1024 654%nat then Z.of_nat 654%nat else 1%Z) * ((if zz_in_Pn 1024 655%nat then Z.of_nat 655%nat else 1%Z) * (if zz_in_Pn 1024 656%nat then Z.of_nat 656%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_656.
    rewrite piu_zz_inPn_1024_655.
    rewrite piu_zz_inPn_1024_654.
    rewrite piu_zz_inPn_1024_653.
    rewrite piu_zz_inPn_1024_652.
    rewrite piu_zz_inPn_1024_651.
    rewrite piu_zz_inPn_1024_650.
    rewrite piu_zz_inPn_1024_649.
    rewrite piu_zz_inPn_1024_648.
    rewrite piu_zz_inPn_1024_647.
    rewrite piu_zz_inPn_1024_646.
    rewrite piu_zz_inPn_1024_645.
    rewrite piu_zz_inPn_1024_644.
    rewrite piu_zz_inPn_1024_643.
    rewrite piu_zz_inPn_1024_642.
    rewrite piu_zz_inPn_1024_641.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb88 : piu_zz_zprod_seg 1024%nat (512%nat + 112%nat) 16%nat = ((if zz_in_Pn 1024 625%nat then Z.of_nat 625%nat else 1%Z) * ((if zz_in_Pn 1024 626%nat then Z.of_nat 626%nat else 1%Z) * ((if zz_in_Pn 1024 627%nat then Z.of_nat 627%nat else 1%Z) * ((if zz_in_Pn 1024 628%nat then Z.of_nat 628%nat else 1%Z) * ((if zz_in_Pn 1024 629%nat then Z.of_nat 629%nat else 1%Z) * ((if zz_in_Pn 1024 630%nat then Z.of_nat 630%nat else 1%Z) * ((if zz_in_Pn 1024 631%nat then Z.of_nat 631%nat else 1%Z) * ((if zz_in_Pn 1024 632%nat then Z.of_nat 632%nat else 1%Z) * ((if zz_in_Pn 1024 633%nat then Z.of_nat 633%nat else 1%Z) * ((if zz_in_Pn 1024 634%nat then Z.of_nat 634%nat else 1%Z) * ((if zz_in_Pn 1024 635%nat then Z.of_nat 635%nat else 1%Z) * ((if zz_in_Pn 1024 636%nat then Z.of_nat 636%nat else 1%Z) * ((if zz_in_Pn 1024 637%nat then Z.of_nat 637%nat else 1%Z) * ((if zz_in_Pn 1024 638%nat then Z.of_nat 638%nat else 1%Z) * ((if zz_in_Pn 1024 639%nat then Z.of_nat 639%nat else 1%Z) * (if zz_in_Pn 1024 640%nat then Z.of_nat 640%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_640.
    rewrite piu_zz_inPn_1024_639.
    rewrite piu_zz_inPn_1024_638.
    rewrite piu_zz_inPn_1024_637.
    rewrite piu_zz_inPn_1024_636.
    rewrite piu_zz_inPn_1024_635.
    rewrite piu_zz_inPn_1024_634.
    rewrite piu_zz_inPn_1024_633.
    rewrite piu_zz_inPn_1024_632.
    rewrite piu_zz_inPn_1024_631.
    rewrite piu_zz_inPn_1024_630.
    rewrite piu_zz_inPn_1024_629.
    rewrite piu_zz_inPn_1024_628.
    rewrite piu_zz_inPn_1024_627.
    rewrite piu_zz_inPn_1024_626.
    rewrite piu_zz_inPn_1024_625.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb89 : piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) 16%nat = ((if zz_in_Pn 1024 609%nat then Z.of_nat 609%nat else 1%Z) * ((if zz_in_Pn 1024 610%nat then Z.of_nat 610%nat else 1%Z) * ((if zz_in_Pn 1024 611%nat then Z.of_nat 611%nat else 1%Z) * ((if zz_in_Pn 1024 612%nat then Z.of_nat 612%nat else 1%Z) * ((if zz_in_Pn 1024 613%nat then Z.of_nat 613%nat else 1%Z) * ((if zz_in_Pn 1024 614%nat then Z.of_nat 614%nat else 1%Z) * ((if zz_in_Pn 1024 615%nat then Z.of_nat 615%nat else 1%Z) * ((if zz_in_Pn 1024 616%nat then Z.of_nat 616%nat else 1%Z) * ((if zz_in_Pn 1024 617%nat then Z.of_nat 617%nat else 1%Z) * ((if zz_in_Pn 1024 618%nat then Z.of_nat 618%nat else 1%Z) * ((if zz_in_Pn 1024 619%nat then Z.of_nat 619%nat else 1%Z) * ((if zz_in_Pn 1024 620%nat then Z.of_nat 620%nat else 1%Z) * ((if zz_in_Pn 1024 621%nat then Z.of_nat 621%nat else 1%Z) * ((if zz_in_Pn 1024 622%nat then Z.of_nat 622%nat else 1%Z) * ((if zz_in_Pn 1024 623%nat then Z.of_nat 623%nat else 1%Z) * (if zz_in_Pn 1024 624%nat then Z.of_nat 624%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_624.
    rewrite piu_zz_inPn_1024_623.
    rewrite piu_zz_inPn_1024_622.
    rewrite piu_zz_inPn_1024_621.
    rewrite piu_zz_inPn_1024_620.
    rewrite piu_zz_inPn_1024_619.
    rewrite piu_zz_inPn_1024_618.
    rewrite piu_zz_inPn_1024_617.
    rewrite piu_zz_inPn_1024_616.
    rewrite piu_zz_inPn_1024_615.
    rewrite piu_zz_inPn_1024_614.
    rewrite piu_zz_inPn_1024_613.
    rewrite piu_zz_inPn_1024_612.
    rewrite piu_zz_inPn_1024_611.
    rewrite piu_zz_inPn_1024_610.
    rewrite piu_zz_inPn_1024_609.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb90 : piu_zz_zprod_seg 1024%nat (512%nat + 80%nat) 16%nat = ((if zz_in_Pn 1024 593%nat then Z.of_nat 593%nat else 1%Z) * ((if zz_in_Pn 1024 594%nat then Z.of_nat 594%nat else 1%Z) * ((if zz_in_Pn 1024 595%nat then Z.of_nat 595%nat else 1%Z) * ((if zz_in_Pn 1024 596%nat then Z.of_nat 596%nat else 1%Z) * ((if zz_in_Pn 1024 597%nat then Z.of_nat 597%nat else 1%Z) * ((if zz_in_Pn 1024 598%nat then Z.of_nat 598%nat else 1%Z) * ((if zz_in_Pn 1024 599%nat then Z.of_nat 599%nat else 1%Z) * ((if zz_in_Pn 1024 600%nat then Z.of_nat 600%nat else 1%Z) * ((if zz_in_Pn 1024 601%nat then Z.of_nat 601%nat else 1%Z) * ((if zz_in_Pn 1024 602%nat then Z.of_nat 602%nat else 1%Z) * ((if zz_in_Pn 1024 603%nat then Z.of_nat 603%nat else 1%Z) * ((if zz_in_Pn 1024 604%nat then Z.of_nat 604%nat else 1%Z) * ((if zz_in_Pn 1024 605%nat then Z.of_nat 605%nat else 1%Z) * ((if zz_in_Pn 1024 606%nat then Z.of_nat 606%nat else 1%Z) * ((if zz_in_Pn 1024 607%nat then Z.of_nat 607%nat else 1%Z) * (if zz_in_Pn 1024 608%nat then Z.of_nat 608%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_608.
    rewrite piu_zz_inPn_1024_607.
    rewrite piu_zz_inPn_1024_606.
    rewrite piu_zz_inPn_1024_605.
    rewrite piu_zz_inPn_1024_604.
    rewrite piu_zz_inPn_1024_603.
    rewrite piu_zz_inPn_1024_602.
    rewrite piu_zz_inPn_1024_601.
    rewrite piu_zz_inPn_1024_600.
    rewrite piu_zz_inPn_1024_599.
    rewrite piu_zz_inPn_1024_598.
    rewrite piu_zz_inPn_1024_597.
    rewrite piu_zz_inPn_1024_596.
    rewrite piu_zz_inPn_1024_595.
    rewrite piu_zz_inPn_1024_594.
    rewrite piu_zz_inPn_1024_593.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb91 : piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 16%nat = ((if zz_in_Pn 1024 577%nat then Z.of_nat 577%nat else 1%Z) * ((if zz_in_Pn 1024 578%nat then Z.of_nat 578%nat else 1%Z) * ((if zz_in_Pn 1024 579%nat then Z.of_nat 579%nat else 1%Z) * ((if zz_in_Pn 1024 580%nat then Z.of_nat 580%nat else 1%Z) * ((if zz_in_Pn 1024 581%nat then Z.of_nat 581%nat else 1%Z) * ((if zz_in_Pn 1024 582%nat then Z.of_nat 582%nat else 1%Z) * ((if zz_in_Pn 1024 583%nat then Z.of_nat 583%nat else 1%Z) * ((if zz_in_Pn 1024 584%nat then Z.of_nat 584%nat else 1%Z) * ((if zz_in_Pn 1024 585%nat then Z.of_nat 585%nat else 1%Z) * ((if zz_in_Pn 1024 586%nat then Z.of_nat 586%nat else 1%Z) * ((if zz_in_Pn 1024 587%nat then Z.of_nat 587%nat else 1%Z) * ((if zz_in_Pn 1024 588%nat then Z.of_nat 588%nat else 1%Z) * ((if zz_in_Pn 1024 589%nat then Z.of_nat 589%nat else 1%Z) * ((if zz_in_Pn 1024 590%nat then Z.of_nat 590%nat else 1%Z) * ((if zz_in_Pn 1024 591%nat then Z.of_nat 591%nat else 1%Z) * (if zz_in_Pn 1024 592%nat then Z.of_nat 592%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_592.
    rewrite piu_zz_inPn_1024_591.
    rewrite piu_zz_inPn_1024_590.
    rewrite piu_zz_inPn_1024_589.
    rewrite piu_zz_inPn_1024_588.
    rewrite piu_zz_inPn_1024_587.
    rewrite piu_zz_inPn_1024_586.
    rewrite piu_zz_inPn_1024_585.
    rewrite piu_zz_inPn_1024_584.
    rewrite piu_zz_inPn_1024_583.
    rewrite piu_zz_inPn_1024_582.
    rewrite piu_zz_inPn_1024_581.
    rewrite piu_zz_inPn_1024_580.
    rewrite piu_zz_inPn_1024_579.
    rewrite piu_zz_inPn_1024_578.
    rewrite piu_zz_inPn_1024_577.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb92 : piu_zz_zprod_seg 1024%nat (512%nat + 48%nat) 16%nat = ((if zz_in_Pn 1024 561%nat then Z.of_nat 561%nat else 1%Z) * ((if zz_in_Pn 1024 562%nat then Z.of_nat 562%nat else 1%Z) * ((if zz_in_Pn 1024 563%nat then Z.of_nat 563%nat else 1%Z) * ((if zz_in_Pn 1024 564%nat then Z.of_nat 564%nat else 1%Z) * ((if zz_in_Pn 1024 565%nat then Z.of_nat 565%nat else 1%Z) * ((if zz_in_Pn 1024 566%nat then Z.of_nat 566%nat else 1%Z) * ((if zz_in_Pn 1024 567%nat then Z.of_nat 567%nat else 1%Z) * ((if zz_in_Pn 1024 568%nat then Z.of_nat 568%nat else 1%Z) * ((if zz_in_Pn 1024 569%nat then Z.of_nat 569%nat else 1%Z) * ((if zz_in_Pn 1024 570%nat then Z.of_nat 570%nat else 1%Z) * ((if zz_in_Pn 1024 571%nat then Z.of_nat 571%nat else 1%Z) * ((if zz_in_Pn 1024 572%nat then Z.of_nat 572%nat else 1%Z) * ((if zz_in_Pn 1024 573%nat then Z.of_nat 573%nat else 1%Z) * ((if zz_in_Pn 1024 574%nat then Z.of_nat 574%nat else 1%Z) * ((if zz_in_Pn 1024 575%nat then Z.of_nat 575%nat else 1%Z) * (if zz_in_Pn 1024 576%nat then Z.of_nat 576%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_576.
    rewrite piu_zz_inPn_1024_575.
    rewrite piu_zz_inPn_1024_574.
    rewrite piu_zz_inPn_1024_573.
    rewrite piu_zz_inPn_1024_572.
    rewrite piu_zz_inPn_1024_571.
    rewrite piu_zz_inPn_1024_570.
    rewrite piu_zz_inPn_1024_569.
    rewrite piu_zz_inPn_1024_568.
    rewrite piu_zz_inPn_1024_567.
    rewrite piu_zz_inPn_1024_566.
    rewrite piu_zz_inPn_1024_565.
    rewrite piu_zz_inPn_1024_564.
    rewrite piu_zz_inPn_1024_563.
    rewrite piu_zz_inPn_1024_562.
    rewrite piu_zz_inPn_1024_561.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb93 : piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) 16%nat = ((if zz_in_Pn 1024 545%nat then Z.of_nat 545%nat else 1%Z) * ((if zz_in_Pn 1024 546%nat then Z.of_nat 546%nat else 1%Z) * ((if zz_in_Pn 1024 547%nat then Z.of_nat 547%nat else 1%Z) * ((if zz_in_Pn 1024 548%nat then Z.of_nat 548%nat else 1%Z) * ((if zz_in_Pn 1024 549%nat then Z.of_nat 549%nat else 1%Z) * ((if zz_in_Pn 1024 550%nat then Z.of_nat 550%nat else 1%Z) * ((if zz_in_Pn 1024 551%nat then Z.of_nat 551%nat else 1%Z) * ((if zz_in_Pn 1024 552%nat then Z.of_nat 552%nat else 1%Z) * ((if zz_in_Pn 1024 553%nat then Z.of_nat 553%nat else 1%Z) * ((if zz_in_Pn 1024 554%nat then Z.of_nat 554%nat else 1%Z) * ((if zz_in_Pn 1024 555%nat then Z.of_nat 555%nat else 1%Z) * ((if zz_in_Pn 1024 556%nat then Z.of_nat 556%nat else 1%Z) * ((if zz_in_Pn 1024 557%nat then Z.of_nat 557%nat else 1%Z) * ((if zz_in_Pn 1024 558%nat then Z.of_nat 558%nat else 1%Z) * ((if zz_in_Pn 1024 559%nat then Z.of_nat 559%nat else 1%Z) * (if zz_in_Pn 1024 560%nat then Z.of_nat 560%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_560.
    rewrite piu_zz_inPn_1024_559.
    rewrite piu_zz_inPn_1024_558.
    rewrite piu_zz_inPn_1024_557.
    rewrite piu_zz_inPn_1024_556.
    rewrite piu_zz_inPn_1024_555.
    rewrite piu_zz_inPn_1024_554.
    rewrite piu_zz_inPn_1024_553.
    rewrite piu_zz_inPn_1024_552.
    rewrite piu_zz_inPn_1024_551.
    rewrite piu_zz_inPn_1024_550.
    rewrite piu_zz_inPn_1024_549.
    rewrite piu_zz_inPn_1024_548.
    rewrite piu_zz_inPn_1024_547.
    rewrite piu_zz_inPn_1024_546.
    rewrite piu_zz_inPn_1024_545.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb94 : piu_zz_zprod_seg 1024%nat (512%nat + 16%nat) 16%nat = ((if zz_in_Pn 1024 529%nat then Z.of_nat 529%nat else 1%Z) * ((if zz_in_Pn 1024 530%nat then Z.of_nat 530%nat else 1%Z) * ((if zz_in_Pn 1024 531%nat then Z.of_nat 531%nat else 1%Z) * ((if zz_in_Pn 1024 532%nat then Z.of_nat 532%nat else 1%Z) * ((if zz_in_Pn 1024 533%nat then Z.of_nat 533%nat else 1%Z) * ((if zz_in_Pn 1024 534%nat then Z.of_nat 534%nat else 1%Z) * ((if zz_in_Pn 1024 535%nat then Z.of_nat 535%nat else 1%Z) * ((if zz_in_Pn 1024 536%nat then Z.of_nat 536%nat else 1%Z) * ((if zz_in_Pn 1024 537%nat then Z.of_nat 537%nat else 1%Z) * ((if zz_in_Pn 1024 538%nat then Z.of_nat 538%nat else 1%Z) * ((if zz_in_Pn 1024 539%nat then Z.of_nat 539%nat else 1%Z) * ((if zz_in_Pn 1024 540%nat then Z.of_nat 540%nat else 1%Z) * ((if zz_in_Pn 1024 541%nat then Z.of_nat 541%nat else 1%Z) * ((if zz_in_Pn 1024 542%nat then Z.of_nat 542%nat else 1%Z) * ((if zz_in_Pn 1024 543%nat then Z.of_nat 543%nat else 1%Z) * (if zz_in_Pn 1024 544%nat then Z.of_nat 544%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_544.
    rewrite piu_zz_inPn_1024_543.
    rewrite piu_zz_inPn_1024_542.
    rewrite piu_zz_inPn_1024_541.
    rewrite piu_zz_inPn_1024_540.
    rewrite piu_zz_inPn_1024_539.
    rewrite piu_zz_inPn_1024_538.
    rewrite piu_zz_inPn_1024_537.
    rewrite piu_zz_inPn_1024_536.
    rewrite piu_zz_inPn_1024_535.
    rewrite piu_zz_inPn_1024_534.
    rewrite piu_zz_inPn_1024_533.
    rewrite piu_zz_inPn_1024_532.
    rewrite piu_zz_inPn_1024_531.
    rewrite piu_zz_inPn_1024_530.
    rewrite piu_zz_inPn_1024_529.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  assert (Hb95 : piu_zz_zprod_seg 1024%nat 512%nat 16%nat = ((if zz_in_Pn 1024 513%nat then Z.of_nat 513%nat else 1%Z) * ((if zz_in_Pn 1024 514%nat then Z.of_nat 514%nat else 1%Z) * ((if zz_in_Pn 1024 515%nat then Z.of_nat 515%nat else 1%Z) * ((if zz_in_Pn 1024 516%nat then Z.of_nat 516%nat else 1%Z) * ((if zz_in_Pn 1024 517%nat then Z.of_nat 517%nat else 1%Z) * ((if zz_in_Pn 1024 518%nat then Z.of_nat 518%nat else 1%Z) * ((if zz_in_Pn 1024 519%nat then Z.of_nat 519%nat else 1%Z) * ((if zz_in_Pn 1024 520%nat then Z.of_nat 520%nat else 1%Z) * ((if zz_in_Pn 1024 521%nat then Z.of_nat 521%nat else 1%Z) * ((if zz_in_Pn 1024 522%nat then Z.of_nat 522%nat else 1%Z) * ((if zz_in_Pn 1024 523%nat then Z.of_nat 523%nat else 1%Z) * ((if zz_in_Pn 1024 524%nat then Z.of_nat 524%nat else 1%Z) * ((if zz_in_Pn 1024 525%nat then Z.of_nat 525%nat else 1%Z) * ((if zz_in_Pn 1024 526%nat then Z.of_nat 526%nat else 1%Z) * ((if zz_in_Pn 1024 527%nat then Z.of_nat 527%nat else 1%Z) * (if zz_in_Pn 1024 528%nat then Z.of_nat 528%nat else 1%Z))))))))))))))))).
  {
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_528.
    rewrite piu_zz_inPn_1024_527.
    rewrite piu_zz_inPn_1024_526.
    rewrite piu_zz_inPn_1024_525.
    rewrite piu_zz_inPn_1024_524.
    rewrite piu_zz_inPn_1024_523.
    rewrite piu_zz_inPn_1024_522.
    rewrite piu_zz_inPn_1024_521.
    rewrite piu_zz_inPn_1024_520.
    rewrite piu_zz_inPn_1024_519.
    rewrite piu_zz_inPn_1024_518.
    rewrite piu_zz_inPn_1024_517.
    rewrite piu_zz_inPn_1024_516.
    rewrite piu_zz_inPn_1024_515.
    rewrite piu_zz_inPn_1024_514.
    rewrite piu_zz_inPn_1024_513.
    cbn [piu_zz_zprod_seg]. reflexivity.
  }
  rewrite Hb0.
  rewrite Hb1.
  rewrite Hb2.
  rewrite Hb3.
  rewrite Hb4.
  rewrite Hb5.
  rewrite Hb6.
  rewrite Hb7.
  rewrite Hb8.
  rewrite Hb9.
  rewrite Hb10.
  rewrite Hb11.
  rewrite Hb12.
  rewrite Hb13.
  rewrite Hb14.
  rewrite Hb15.
  rewrite Hb16.
  rewrite Hb17.
  rewrite Hb18.
  rewrite Hb19.
  rewrite Hb20.
  rewrite Hb21.
  rewrite Hb22.
  rewrite Hb23.
  rewrite Hb24.
  rewrite Hb25.
  rewrite Hb26.
  rewrite Hb27.
  rewrite Hb28.
  rewrite Hb29.
  rewrite Hb30.
  rewrite Hb31.
  rewrite Hb32.
  rewrite Hb33.
  rewrite Hb34.
  rewrite Hb35.
  rewrite Hb36.
  rewrite Hb37.
  rewrite Hb38.
  rewrite Hb39.
  rewrite Hb40.
  rewrite Hb41.
  rewrite Hb42.
  rewrite Hb43.
  rewrite Hb44.
  rewrite Hb45.
  rewrite Hb46.
  rewrite Hb47.
  rewrite Hb48.
  rewrite Hb49.
  rewrite Hb50.
  rewrite Hb51.
  rewrite Hb52.
  rewrite Hb53.
  rewrite Hb54.
  rewrite Hb55.
  rewrite Hb56.
  rewrite Hb57.
  rewrite Hb58.
  rewrite Hb59.
  rewrite Hb60.
  rewrite Hb61.
  rewrite Hb62.
  rewrite Hb63.
  rewrite Hb64.
  rewrite Hb65.
  rewrite Hb66.
  rewrite Hb67.
  rewrite Hb68.
  rewrite Hb69.
  rewrite Hb70.
  rewrite Hb71.
  rewrite Hb72.
  rewrite Hb73.
  rewrite Hb74.
  rewrite Hb75.
  rewrite Hb76.
  rewrite Hb77.
  rewrite Hb78.
  rewrite Hb79.
  rewrite Hb80.
  rewrite Hb81.
  rewrite Hb82.
  rewrite Hb83.
  rewrite Hb84.
  rewrite Hb85.
  rewrite Hb86.
  rewrite Hb87.
  rewrite Hb88.
  rewrite Hb89.
  rewrite Hb90.
  rewrite Hb91.
  rewrite Hb92.
  rewrite Hb93.
  rewrite Hb94.
  rewrite Hb95.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_zzL_256 : Z := 1439600395983207151961998095837161107743970738136801543275685520784991600085843173050963312415906468026169421543914322197833330831776574600079802607987349212604698534075440200924252773657659076289845969292665683777159179673587968208659406896508657114739009185278888590298085369370870580824155069081588978598645352141299672184681729566325420988919325142557734891374571173760000%Z.
Lemma piu_zz_zzL_256 : zz_L 256 = piu_zz_lit_zzL_256.
Proof.
  unfold zz_L.
  replace (4 * 256)%nat with 1024%nat by lia.
  rewrite piu_zz_lcmr_1024, piu_zz_zzPhi_256.
  symmetry.
  apply (Z.div_unique piu_zz_lit_lcm_1024 piu_zz_lit_Phi_256 piu_zz_lit_zzL_256 0%Z).
  - unfold piu_zz_lit_Phi_256. lia.
  - vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_zzL_512 : Z := 118825846924092304628618327583286017009039493305617286577384751064894263170557136817184388428956473183602436322326443000231857299878173734617732544579394364010298081515796785398873628482386730783620244613767421708787093780371265975267395310352347879475337940127689458490709184420417527497070925395304548973759471408899350114828210768953422143798436021918330105446331231222330866857005349916314237598982020817489660410851587586179142017698738313360002046996904975766498230044101311617982821785743505288056912957446744926991217542499843165454256336715181300432169624114317204038202527796434491690892197511453842459788435810086055586017431601792332448138412341938715508992333079029284800796671166778314377198359091018983894892246192258046361771010443520000%Z.
Lemma piu_zz_zzL_512 : zz_L 512 = piu_zz_lit_zzL_512.
Proof.
  unfold zz_L.
  replace (4 * 512)%nat with 2048%nat by lia.
  rewrite piu_zz_lcmr_2048, piu_zz_zzPhi_512.
  symmetry.
  apply (Z.div_unique piu_zz_lit_lcm_2048 piu_zz_lit_Phi_512 piu_zz_lit_zzL_512 0%Z).
  - unfold piu_zz_lit_Phi_512. lia.
  - vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_zzL_1024 : Z := 24674028657899334466432502778974052037199858988697439266991449029817392868484218026233200150474541265702268630146307900299327853914636821412779688380294754692968663733921112980793895857900225712291654710710097813513442044572286259525469992541493074359895544467270641640893841685689100251558874750988007353118199550187610428283725611537990807621714190768788485832725865190531046433844933935403789267675127624748564853307164671257357410511434059674829904024476784240423328458005708052351522795095678241826896061892028996743433072006914691239885773787537027129707833155756361238992042812807420984241980955007641171463463903740678350310209855226714621437862909571720715155690635008330609940023202696055227631234903487880106909895128068721200776182594229621728929224167792281971999296970973948353506434876938081145001894373831909192528904730089978004559333487881063669307595697531910823612572548108214262142214130924028895780481225054792407930862629575578040211676981710484156171471244572905685907257058189892863900311082209394335074448311338924183872492492663473767324634393027084892712434784454506695451658344294868109603372554369478742596768146169981074185443076317737842025136525835144490085522088930952381210172655370919009621918536528081860997632321233895951384367960515897280191863751281988533696746590802466337838459699347265037231840379688930571061014792779156864930320933799478128608639761210058775703752641732382679232618464820358110259831022230181641703996229631404640371609726002628413109491200000%Z.
Lemma piu_zz_zzL_1024 : zz_L 1024 = piu_zz_lit_zzL_1024.
Proof.
  unfold zz_L.
  replace (4 * 1024)%nat with 4096%nat by lia.
  rewrite piu_zz_lcmr_4096, piu_zz_zzPhi_1024.
  symmetry.
  apply (Z.div_unique piu_zz_lit_lcm_4096 piu_zz_lit_Phi_1024 piu_zz_lit_zzL_1024 0%Z).
  - unfold piu_zz_lit_Phi_1024. lia.
  - vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_qpow_u_256 : Q := (236530670083543041291695849287757761206140688803450339044681859048673693207594496123036763419789924804096709668655515654656670000847596964020814760550047269613263893135633671672504615936263534463112215069370086973340068509866244038087786645948344559191967510601952535706685695261478670962920092330778205839314415566627024539002282528137603437920441249982600907754811695928321 # 1)%Q.
Lemma piu_zz_qpow_u_256 : piu_zz_qpow piu_zz_lam_u 256 = piu_zz_lit_qpow_u_256.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_qpow_u_512 : Q := (55946757890169883068104409084770729789817333850615146050414778950108986015056593684055981111769100272647753704747854816820626269410158467176374426416844190646056126100511427731945363395105463444333366988508151452888053106876679579436824047753643644453960284652897953833731681862864022280818227391598119643020102100797198571208848436532255866850429798087402402157708380127890312014075244140380097990929153883309069059191668094556766699472601170995762763557576625466913463620701117699423351390386805156732039098786966356920713176933339769821547378108286044588558179341727823292218156172567728948076085302457567299472085048394130527727907433129381558690679321462986895430051900920373843757027098681702658216297620719277955062351539484482120889969879041 # 1)%Q.
Lemma piu_zz_qpow_u_512 : piu_zz_qpow piu_zz_lam_u 512 = piu_zz_lit_qpow_u_512.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_qpow_u_1024 : Q := (3130039718421286065861724372871197578714348677094902996406662958514098462122129372412308909215645504945874454883438400941414229256198782827598748898508233643614039457786415026002729706654763268460193647094400294147711657769721363197181128752629538123620507852624646860645084661848825349124870091849393517242865671039049627058308230773584884976580579818392365841173532239548974794964221271839388411937647603605362216972916523775395080484540952522149791806742888881749105811457639989810366227367230875060980226640042509792452360198049354034215231458080969949857388342166096632111114740185915762588473517438845561793202824623924414320739534076825629717076603809391979245178276281654505466433601017942538223423377932163035887661560915404054196324537233564419996785352268208250667837288040699984668625231682880023061221009506069203919007461075653859211515181908099115596514268992834572550014240211363560129279426298204530575152569696504953815015869127303523720975949770142089419487156497658718863414933297202507928608304283043078512583488313824960018888839658915395032995288107968986512652835630557894160381263049398409829482939794150551421523002608131883809217388872174370570693959725016023851592832655102379648630608894753068625998343818103655499410867281014470098256414879003501905817547025453953873250651121659290186213529578302628510617999254563704345947507185094122727886030985060676260553580828997915363609665501268423783053577756315310189369738144197927002085951015743776457900879440252171079681 # 1)%Q.
Lemma piu_zz_qpow_u_1024 : piu_zz_qpow piu_zz_lam_u 1024 = piu_zz_lit_qpow_u_1024.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_qpow_l_256 : Q := (29679461958421860027474672036392063098329257234581089128345526431723979545552115729782617835010302855624239928653858292249457713280740298929143321907869859733471841316163995030278059385497844537226800339797504748629648456127367514350797020913965997694320062466543470334721541973597411433743834329686895201976264603184906336746737469956388347749325879054460171894386589696 # 1)%Q.
Lemma piu_zz_qpow_l_256 : piu_zz_qpow piu_zz_lam_l 256 = piu_zz_lit_qpow_l_256.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_qpow_l_512 : Q := (880870462141410351038248692908030187645399921888917790000020056539301378243065309236208346321922683482743736146676393083315539449023128907628176358118308931835300504103634744537797119006690495704215650283644158804093414456919000009899596206191905975872070370119190674426491892244846506959208170502112863779854241131079974296194652841201985674800567211420960219365163400510930380487868088315823698972620559659870030836966111073570534106146073803095950890865963378996620562876328706597997015163333010012288720441474649201131656583116998987914631117590399022028650011980703734472886653563482423889528026219236652883433775561592660833014234995465193143694116855191932562851389787361958983807228877821010398119908326301220597829367860041053372416 # 1)%Q.
Lemma piu_zz_qpow_l_512 : piu_zz_qpow piu_zz_lam_l 512 = piu_zz_lit_qpow_l_512.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_qpow_l_1024 : Q := (775932771073221846521285498966346072982594724354346384466463225147822047292699062480114400878371323505292447132811145266298695716476865522068955019488994930773530808500032231725898699344115265603658947732805940281620547007035151312600520204324784471290004827214015725196927271078590665083444179305679949954559677477798677303054987523759836792865271280776059528577868167557582249229461151546123710424269446845779635864544243431378366646726520404673750591077371728708946889456590389095398900767733252883028146052538892936180726801801517219590776552981803870003923311213542600629417510509820121907927703414296112008911406126141884962964926854799279057041504530491290026625096742972646182819477513065462305153575384817642735257677053842618353357197079535337302504972853573604246528936305585854755951349450020363904891512305661092748006195843958182892735176954627424551684625416614473023994120467356359215339631358968857934769602341909052128656844745398026987120934363236928993938925682015081533969338236402882351313801599560355803474235580941087950312475978801873925110578314842608376532296940918204075008032569321369252005600822212729123705595880029400766933413566585199576101296867768029402768436321232235307193139819408861036243161322719586148030410653492909385952172240885806296329015156846538065241705440656737288454108080435690550077206880496006262919446496117848914727299769404801184877080282148200603129146363738231078377899280945136539018322401197097999958567278906726789677056 # 1)%Q.
Lemma piu_zz_qpow_l_1024 : piu_zz_qpow piu_zz_lam_l 1024 = piu_zz_lit_qpow_l_1024.
Proof. vm_compute. reflexivity. Qed.

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

