(* piu_zz_tau_enclosure_phi1024.v — consumer 六片链末棒四片机械拆分（KB10 影子链候选案）第 2/4 片·真依赖图波 1。
   使命：承载 zzPhi_1024 单引理巨证体（原 β 区 L811-3133，语句边界不可内切区整块迁移）。
   依赖：piu_zz_tau_enclosure_bank4（直接式 Require Import·伞链 bank3..1/base 传递覆盖 inPn_1024 表与 lcm 面）、
   piu_zz_poincare_engine（zz_in_Pn/zprod_seg）、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   真图证据：对 head 六名 grep 零命中（不依赖 head，与 head 同属波 1 互独立）。
   对标：piu_zz_tau_enclosure 原单件（六片链末棒再拆，语句面逐字节等价）。
   构造性：本片语句零假设、零公理。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_enclosure_phi1024.v *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Export piu_zz_tau_hb_wave1.
Require Export piu_zz_tau_hb_wave2.
Require Export piu_zz_tau_hb_wave3a.
Require Export piu_zz_tau_hb_wave3b.
Require Export piu_zz_tau_hb_wave3c.
Require Export piu_zz_tau_hb_wave3d.
Require Export piu_zz_tau_hb_wave4a.
Require Export piu_zz_tau_hb_wave4b.
Require Export piu_zz_tau_hb_wave4c.
Require Export piu_zz_tau_hb_wave4d.
Require Export piu_zz_tau_hb_wave5.
Require Export piu_zz_tau_hb_wave6.
Require Export piu_zz_tau_hb_wave7.
Require Export piu_zz_tau_hb_wave8.
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
  assert (Hb0 := piu_zz_hb_1024_0).
  assert (Hb1 := piu_zz_hb_1024_1).
  assert (Hb2 := piu_zz_hb_1024_2).
  assert (Hb3 := piu_zz_hb_1024_3).
  assert (Hb4 := piu_zz_hb_1024_4).
  assert (Hb5 := piu_zz_hb_1024_5).
  assert (Hb6 := piu_zz_hb_1024_6).
  assert (Hb7 := piu_zz_hb_1024_7).
  assert (Hb8 := piu_zz_hb_1024_8).
  assert (Hb9 := piu_zz_hb_1024_9).
  assert (Hb10 := piu_zz_hb_1024_10).
  assert (Hb11 := piu_zz_hb_1024_11).
  assert (Hb12 := piu_zz_hb_1024_12).
  assert (Hb13 := piu_zz_hb_1024_13).
  assert (Hb14 := piu_zz_hb_1024_14).
  assert (Hb15 := piu_zz_hb_1024_15).
  assert (Hb16 := piu_zz_hb_1024_16).
  assert (Hb17 := piu_zz_hb_1024_17).
  assert (Hb18 := piu_zz_hb_1024_18).
  assert (Hb19 := piu_zz_hb_1024_19).
  assert (Hb20 := piu_zz_hb_1024_20).
  assert (Hb21 := piu_zz_hb_1024_21).
  assert (Hb22 := piu_zz_hb_1024_22).
  assert (Hb23 := piu_zz_hb_1024_23).
  assert (Hb24 := piu_zz_hb_1024_24).
  assert (Hb25 := piu_zz_hb_1024_25).
  assert (Hb26 := piu_zz_hb_1024_26).
  assert (Hb27 := piu_zz_hb_1024_27).
  assert (Hb28 := piu_zz_hb_1024_28).
  assert (Hb29 := piu_zz_hb_1024_29).
  assert (Hb30 := piu_zz_hb_1024_30).
  assert (Hb31 := piu_zz_hb_1024_31).
  assert (Hb32 := piu_zz_hb_1024_32).
  assert (Hb33 := piu_zz_hb_1024_33).
  assert (Hb34 := piu_zz_hb_1024_34).
  assert (Hb35 := piu_zz_hb_1024_35).
  assert (Hb36 := piu_zz_hb_1024_36).
  assert (Hb37 := piu_zz_hb_1024_37).
  assert (Hb38 := piu_zz_hb_1024_38).
  assert (Hb39 := piu_zz_hb_1024_39).
  assert (Hb40 := piu_zz_hb_1024_40).
  assert (Hb41 := piu_zz_hb_1024_41).
  assert (Hb42 := piu_zz_hb_1024_42).
  assert (Hb43 := piu_zz_hb_1024_43).
  assert (Hb44 := piu_zz_hb_1024_44).
  assert (Hb45 := piu_zz_hb_1024_45).
  assert (Hb46 := piu_zz_hb_1024_46).
  assert (Hb47 := piu_zz_hb_1024_47).
  assert (Hb48 := piu_zz_hb_1024_48).
  assert (Hb49 := piu_zz_hb_1024_49).
  assert (Hb50 := piu_zz_hb_1024_50).
  assert (Hb51 := piu_zz_hb_1024_51).
  assert (Hb52 := piu_zz_hb_1024_52).
  assert (Hb53 := piu_zz_hb_1024_53).
  assert (Hb54 := piu_zz_hb_1024_54).
  assert (Hb55 := piu_zz_hb_1024_55).
  assert (Hb56 := piu_zz_hb_1024_56).
  assert (Hb57 := piu_zz_hb_1024_57).
  assert (Hb58 := piu_zz_hb_1024_58).
  assert (Hb59 := piu_zz_hb_1024_59).
  assert (Hb60 := piu_zz_hb_1024_60).
  assert (Hb61 := piu_zz_hb_1024_61).
  assert (Hb62 := piu_zz_hb_1024_62).
  assert (Hb63 := piu_zz_hb_1024_63).
  assert (Hb64 := piu_zz_hb_1024_64).
  assert (Hb65 := piu_zz_hb_1024_65).
  assert (Hb66 := piu_zz_hb_1024_66).
  assert (Hb67 := piu_zz_hb_1024_67).
  assert (Hb68 := piu_zz_hb_1024_68).
  assert (Hb69 := piu_zz_hb_1024_69).
  assert (Hb70 := piu_zz_hb_1024_70).
  assert (Hb71 := piu_zz_hb_1024_71).
  assert (Hb72 := piu_zz_hb_1024_72).
  assert (Hb73 := piu_zz_hb_1024_73).
  assert (Hb74 := piu_zz_hb_1024_74).
  assert (Hb75 := piu_zz_hb_1024_75).
  assert (Hb76 := piu_zz_hb_1024_76).
  assert (Hb77 := piu_zz_hb_1024_77).
  assert (Hb78 := piu_zz_hb_1024_78).
  assert (Hb79 := piu_zz_hb_1024_79).
  assert (Hb80 := piu_zz_hb_1024_80).
  assert (Hb81 := piu_zz_hb_1024_81).
  assert (Hb82 := piu_zz_hb_1024_82).
  assert (Hb83 := piu_zz_hb_1024_83).
  assert (Hb84 := piu_zz_hb_1024_84).
  assert (Hb85 := piu_zz_hb_1024_85).
  assert (Hb86 := piu_zz_hb_1024_86).
  assert (Hb87 := piu_zz_hb_1024_87).
  assert (Hb88 := piu_zz_hb_1024_88).
  assert (Hb89 := piu_zz_hb_1024_89).
  assert (Hb90 := piu_zz_hb_1024_90).
  assert (Hb91 := piu_zz_hb_1024_91).
  assert (Hb92 := piu_zz_hb_1024_92).
  assert (Hb93 := piu_zz_hb_1024_93).
  assert (Hb94 := piu_zz_hb_1024_94).
  assert (Hb95 := piu_zz_hb_1024_95).
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

