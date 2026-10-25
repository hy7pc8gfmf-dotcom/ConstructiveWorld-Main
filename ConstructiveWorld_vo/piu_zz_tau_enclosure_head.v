(* piu_zz_tau_enclosure_head.v — consumer 六片链末棒四片机械拆分（KB10 影子链候选案）第 1/4 片。
   使命：承载 zz_Phi 256/512 字面值链（原 α 头区 L10-810），供 phi1024/literals/tail 经 Require Export 链传递引用。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
   piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure 原单件（六片链末棒再拆，语句面逐字节等价）。
   构造性：本片语句零假设、零公理。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_enclosure_head.v *)
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
