(* piu_zz_tau_hb_wave2.v — KB11 Hb 升格候选子片 2/8（512 段 Hb16-Hb31·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave2.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L439-L459 (assert Hb16) *)
Lemma piu_zz_hb_512_16 : piu_zz_zprod_seg 512%nat (512%nat + 240%nat) 16%nat = ((if zz_in_Pn 512 753%nat then Z.of_nat 753%nat else 1%Z) * ((if zz_in_Pn 512 754%nat then Z.of_nat 754%nat else 1%Z) * ((if zz_in_Pn 512 755%nat then Z.of_nat 755%nat else 1%Z) * ((if zz_in_Pn 512 756%nat then Z.of_nat 756%nat else 1%Z) * ((if zz_in_Pn 512 757%nat then Z.of_nat 757%nat else 1%Z) * ((if zz_in_Pn 512 758%nat then Z.of_nat 758%nat else 1%Z) * ((if zz_in_Pn 512 759%nat then Z.of_nat 759%nat else 1%Z) * ((if zz_in_Pn 512 760%nat then Z.of_nat 760%nat else 1%Z) * ((if zz_in_Pn 512 761%nat then Z.of_nat 761%nat else 1%Z) * ((if zz_in_Pn 512 762%nat then Z.of_nat 762%nat else 1%Z) * ((if zz_in_Pn 512 763%nat then Z.of_nat 763%nat else 1%Z) * ((if zz_in_Pn 512 764%nat then Z.of_nat 764%nat else 1%Z) * ((if zz_in_Pn 512 765%nat then Z.of_nat 765%nat else 1%Z) * ((if zz_in_Pn 512 766%nat then Z.of_nat 766%nat else 1%Z) * ((if zz_in_Pn 512 767%nat then Z.of_nat 767%nat else 1%Z) * (if zz_in_Pn 512 768%nat then Z.of_nat 768%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L460-L480 (assert Hb17) *)
Lemma piu_zz_hb_512_17 : piu_zz_zprod_seg 512%nat (512%nat + 224%nat) 16%nat = ((if zz_in_Pn 512 737%nat then Z.of_nat 737%nat else 1%Z) * ((if zz_in_Pn 512 738%nat then Z.of_nat 738%nat else 1%Z) * ((if zz_in_Pn 512 739%nat then Z.of_nat 739%nat else 1%Z) * ((if zz_in_Pn 512 740%nat then Z.of_nat 740%nat else 1%Z) * ((if zz_in_Pn 512 741%nat then Z.of_nat 741%nat else 1%Z) * ((if zz_in_Pn 512 742%nat then Z.of_nat 742%nat else 1%Z) * ((if zz_in_Pn 512 743%nat then Z.of_nat 743%nat else 1%Z) * ((if zz_in_Pn 512 744%nat then Z.of_nat 744%nat else 1%Z) * ((if zz_in_Pn 512 745%nat then Z.of_nat 745%nat else 1%Z) * ((if zz_in_Pn 512 746%nat then Z.of_nat 746%nat else 1%Z) * ((if zz_in_Pn 512 747%nat then Z.of_nat 747%nat else 1%Z) * ((if zz_in_Pn 512 748%nat then Z.of_nat 748%nat else 1%Z) * ((if zz_in_Pn 512 749%nat then Z.of_nat 749%nat else 1%Z) * ((if zz_in_Pn 512 750%nat then Z.of_nat 750%nat else 1%Z) * ((if zz_in_Pn 512 751%nat then Z.of_nat 751%nat else 1%Z) * (if zz_in_Pn 512 752%nat then Z.of_nat 752%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L481-L501 (assert Hb18) *)
Lemma piu_zz_hb_512_18 : piu_zz_zprod_seg 512%nat (512%nat + 208%nat) 16%nat = ((if zz_in_Pn 512 721%nat then Z.of_nat 721%nat else 1%Z) * ((if zz_in_Pn 512 722%nat then Z.of_nat 722%nat else 1%Z) * ((if zz_in_Pn 512 723%nat then Z.of_nat 723%nat else 1%Z) * ((if zz_in_Pn 512 724%nat then Z.of_nat 724%nat else 1%Z) * ((if zz_in_Pn 512 725%nat then Z.of_nat 725%nat else 1%Z) * ((if zz_in_Pn 512 726%nat then Z.of_nat 726%nat else 1%Z) * ((if zz_in_Pn 512 727%nat then Z.of_nat 727%nat else 1%Z) * ((if zz_in_Pn 512 728%nat then Z.of_nat 728%nat else 1%Z) * ((if zz_in_Pn 512 729%nat then Z.of_nat 729%nat else 1%Z) * ((if zz_in_Pn 512 730%nat then Z.of_nat 730%nat else 1%Z) * ((if zz_in_Pn 512 731%nat then Z.of_nat 731%nat else 1%Z) * ((if zz_in_Pn 512 732%nat then Z.of_nat 732%nat else 1%Z) * ((if zz_in_Pn 512 733%nat then Z.of_nat 733%nat else 1%Z) * ((if zz_in_Pn 512 734%nat then Z.of_nat 734%nat else 1%Z) * ((if zz_in_Pn 512 735%nat then Z.of_nat 735%nat else 1%Z) * (if zz_in_Pn 512 736%nat then Z.of_nat 736%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L502-L522 (assert Hb19) *)
Lemma piu_zz_hb_512_19 : piu_zz_zprod_seg 512%nat (512%nat + 192%nat) 16%nat = ((if zz_in_Pn 512 705%nat then Z.of_nat 705%nat else 1%Z) * ((if zz_in_Pn 512 706%nat then Z.of_nat 706%nat else 1%Z) * ((if zz_in_Pn 512 707%nat then Z.of_nat 707%nat else 1%Z) * ((if zz_in_Pn 512 708%nat then Z.of_nat 708%nat else 1%Z) * ((if zz_in_Pn 512 709%nat then Z.of_nat 709%nat else 1%Z) * ((if zz_in_Pn 512 710%nat then Z.of_nat 710%nat else 1%Z) * ((if zz_in_Pn 512 711%nat then Z.of_nat 711%nat else 1%Z) * ((if zz_in_Pn 512 712%nat then Z.of_nat 712%nat else 1%Z) * ((if zz_in_Pn 512 713%nat then Z.of_nat 713%nat else 1%Z) * ((if zz_in_Pn 512 714%nat then Z.of_nat 714%nat else 1%Z) * ((if zz_in_Pn 512 715%nat then Z.of_nat 715%nat else 1%Z) * ((if zz_in_Pn 512 716%nat then Z.of_nat 716%nat else 1%Z) * ((if zz_in_Pn 512 717%nat then Z.of_nat 717%nat else 1%Z) * ((if zz_in_Pn 512 718%nat then Z.of_nat 718%nat else 1%Z) * ((if zz_in_Pn 512 719%nat then Z.of_nat 719%nat else 1%Z) * (if zz_in_Pn 512 720%nat then Z.of_nat 720%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L523-L543 (assert Hb20) *)
Lemma piu_zz_hb_512_20 : piu_zz_zprod_seg 512%nat (512%nat + 176%nat) 16%nat = ((if zz_in_Pn 512 689%nat then Z.of_nat 689%nat else 1%Z) * ((if zz_in_Pn 512 690%nat then Z.of_nat 690%nat else 1%Z) * ((if zz_in_Pn 512 691%nat then Z.of_nat 691%nat else 1%Z) * ((if zz_in_Pn 512 692%nat then Z.of_nat 692%nat else 1%Z) * ((if zz_in_Pn 512 693%nat then Z.of_nat 693%nat else 1%Z) * ((if zz_in_Pn 512 694%nat then Z.of_nat 694%nat else 1%Z) * ((if zz_in_Pn 512 695%nat then Z.of_nat 695%nat else 1%Z) * ((if zz_in_Pn 512 696%nat then Z.of_nat 696%nat else 1%Z) * ((if zz_in_Pn 512 697%nat then Z.of_nat 697%nat else 1%Z) * ((if zz_in_Pn 512 698%nat then Z.of_nat 698%nat else 1%Z) * ((if zz_in_Pn 512 699%nat then Z.of_nat 699%nat else 1%Z) * ((if zz_in_Pn 512 700%nat then Z.of_nat 700%nat else 1%Z) * ((if zz_in_Pn 512 701%nat then Z.of_nat 701%nat else 1%Z) * ((if zz_in_Pn 512 702%nat then Z.of_nat 702%nat else 1%Z) * ((if zz_in_Pn 512 703%nat then Z.of_nat 703%nat else 1%Z) * (if zz_in_Pn 512 704%nat then Z.of_nat 704%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L544-L564 (assert Hb21) *)
Lemma piu_zz_hb_512_21 : piu_zz_zprod_seg 512%nat (512%nat + 160%nat) 16%nat = ((if zz_in_Pn 512 673%nat then Z.of_nat 673%nat else 1%Z) * ((if zz_in_Pn 512 674%nat then Z.of_nat 674%nat else 1%Z) * ((if zz_in_Pn 512 675%nat then Z.of_nat 675%nat else 1%Z) * ((if zz_in_Pn 512 676%nat then Z.of_nat 676%nat else 1%Z) * ((if zz_in_Pn 512 677%nat then Z.of_nat 677%nat else 1%Z) * ((if zz_in_Pn 512 678%nat then Z.of_nat 678%nat else 1%Z) * ((if zz_in_Pn 512 679%nat then Z.of_nat 679%nat else 1%Z) * ((if zz_in_Pn 512 680%nat then Z.of_nat 680%nat else 1%Z) * ((if zz_in_Pn 512 681%nat then Z.of_nat 681%nat else 1%Z) * ((if zz_in_Pn 512 682%nat then Z.of_nat 682%nat else 1%Z) * ((if zz_in_Pn 512 683%nat then Z.of_nat 683%nat else 1%Z) * ((if zz_in_Pn 512 684%nat then Z.of_nat 684%nat else 1%Z) * ((if zz_in_Pn 512 685%nat then Z.of_nat 685%nat else 1%Z) * ((if zz_in_Pn 512 686%nat then Z.of_nat 686%nat else 1%Z) * ((if zz_in_Pn 512 687%nat then Z.of_nat 687%nat else 1%Z) * (if zz_in_Pn 512 688%nat then Z.of_nat 688%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L565-L585 (assert Hb22) *)
Lemma piu_zz_hb_512_22 : piu_zz_zprod_seg 512%nat (512%nat + 144%nat) 16%nat = ((if zz_in_Pn 512 657%nat then Z.of_nat 657%nat else 1%Z) * ((if zz_in_Pn 512 658%nat then Z.of_nat 658%nat else 1%Z) * ((if zz_in_Pn 512 659%nat then Z.of_nat 659%nat else 1%Z) * ((if zz_in_Pn 512 660%nat then Z.of_nat 660%nat else 1%Z) * ((if zz_in_Pn 512 661%nat then Z.of_nat 661%nat else 1%Z) * ((if zz_in_Pn 512 662%nat then Z.of_nat 662%nat else 1%Z) * ((if zz_in_Pn 512 663%nat then Z.of_nat 663%nat else 1%Z) * ((if zz_in_Pn 512 664%nat then Z.of_nat 664%nat else 1%Z) * ((if zz_in_Pn 512 665%nat then Z.of_nat 665%nat else 1%Z) * ((if zz_in_Pn 512 666%nat then Z.of_nat 666%nat else 1%Z) * ((if zz_in_Pn 512 667%nat then Z.of_nat 667%nat else 1%Z) * ((if zz_in_Pn 512 668%nat then Z.of_nat 668%nat else 1%Z) * ((if zz_in_Pn 512 669%nat then Z.of_nat 669%nat else 1%Z) * ((if zz_in_Pn 512 670%nat then Z.of_nat 670%nat else 1%Z) * ((if zz_in_Pn 512 671%nat then Z.of_nat 671%nat else 1%Z) * (if zz_in_Pn 512 672%nat then Z.of_nat 672%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L586-L606 (assert Hb23) *)
Lemma piu_zz_hb_512_23 : piu_zz_zprod_seg 512%nat (512%nat + 128%nat) 16%nat = ((if zz_in_Pn 512 641%nat then Z.of_nat 641%nat else 1%Z) * ((if zz_in_Pn 512 642%nat then Z.of_nat 642%nat else 1%Z) * ((if zz_in_Pn 512 643%nat then Z.of_nat 643%nat else 1%Z) * ((if zz_in_Pn 512 644%nat then Z.of_nat 644%nat else 1%Z) * ((if zz_in_Pn 512 645%nat then Z.of_nat 645%nat else 1%Z) * ((if zz_in_Pn 512 646%nat then Z.of_nat 646%nat else 1%Z) * ((if zz_in_Pn 512 647%nat then Z.of_nat 647%nat else 1%Z) * ((if zz_in_Pn 512 648%nat then Z.of_nat 648%nat else 1%Z) * ((if zz_in_Pn 512 649%nat then Z.of_nat 649%nat else 1%Z) * ((if zz_in_Pn 512 650%nat then Z.of_nat 650%nat else 1%Z) * ((if zz_in_Pn 512 651%nat then Z.of_nat 651%nat else 1%Z) * ((if zz_in_Pn 512 652%nat then Z.of_nat 652%nat else 1%Z) * ((if zz_in_Pn 512 653%nat then Z.of_nat 653%nat else 1%Z) * ((if zz_in_Pn 512 654%nat then Z.of_nat 654%nat else 1%Z) * ((if zz_in_Pn 512 655%nat then Z.of_nat 655%nat else 1%Z) * (if zz_in_Pn 512 656%nat then Z.of_nat 656%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L607-L627 (assert Hb24) *)
Lemma piu_zz_hb_512_24 : piu_zz_zprod_seg 512%nat (512%nat + 112%nat) 16%nat = ((if zz_in_Pn 512 625%nat then Z.of_nat 625%nat else 1%Z) * ((if zz_in_Pn 512 626%nat then Z.of_nat 626%nat else 1%Z) * ((if zz_in_Pn 512 627%nat then Z.of_nat 627%nat else 1%Z) * ((if zz_in_Pn 512 628%nat then Z.of_nat 628%nat else 1%Z) * ((if zz_in_Pn 512 629%nat then Z.of_nat 629%nat else 1%Z) * ((if zz_in_Pn 512 630%nat then Z.of_nat 630%nat else 1%Z) * ((if zz_in_Pn 512 631%nat then Z.of_nat 631%nat else 1%Z) * ((if zz_in_Pn 512 632%nat then Z.of_nat 632%nat else 1%Z) * ((if zz_in_Pn 512 633%nat then Z.of_nat 633%nat else 1%Z) * ((if zz_in_Pn 512 634%nat then Z.of_nat 634%nat else 1%Z) * ((if zz_in_Pn 512 635%nat then Z.of_nat 635%nat else 1%Z) * ((if zz_in_Pn 512 636%nat then Z.of_nat 636%nat else 1%Z) * ((if zz_in_Pn 512 637%nat then Z.of_nat 637%nat else 1%Z) * ((if zz_in_Pn 512 638%nat then Z.of_nat 638%nat else 1%Z) * ((if zz_in_Pn 512 639%nat then Z.of_nat 639%nat else 1%Z) * (if zz_in_Pn 512 640%nat then Z.of_nat 640%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L628-L648 (assert Hb25) *)
Lemma piu_zz_hb_512_25 : piu_zz_zprod_seg 512%nat (512%nat + 96%nat) 16%nat = ((if zz_in_Pn 512 609%nat then Z.of_nat 609%nat else 1%Z) * ((if zz_in_Pn 512 610%nat then Z.of_nat 610%nat else 1%Z) * ((if zz_in_Pn 512 611%nat then Z.of_nat 611%nat else 1%Z) * ((if zz_in_Pn 512 612%nat then Z.of_nat 612%nat else 1%Z) * ((if zz_in_Pn 512 613%nat then Z.of_nat 613%nat else 1%Z) * ((if zz_in_Pn 512 614%nat then Z.of_nat 614%nat else 1%Z) * ((if zz_in_Pn 512 615%nat then Z.of_nat 615%nat else 1%Z) * ((if zz_in_Pn 512 616%nat then Z.of_nat 616%nat else 1%Z) * ((if zz_in_Pn 512 617%nat then Z.of_nat 617%nat else 1%Z) * ((if zz_in_Pn 512 618%nat then Z.of_nat 618%nat else 1%Z) * ((if zz_in_Pn 512 619%nat then Z.of_nat 619%nat else 1%Z) * ((if zz_in_Pn 512 620%nat then Z.of_nat 620%nat else 1%Z) * ((if zz_in_Pn 512 621%nat then Z.of_nat 621%nat else 1%Z) * ((if zz_in_Pn 512 622%nat then Z.of_nat 622%nat else 1%Z) * ((if zz_in_Pn 512 623%nat then Z.of_nat 623%nat else 1%Z) * (if zz_in_Pn 512 624%nat then Z.of_nat 624%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L649-L669 (assert Hb26) *)
Lemma piu_zz_hb_512_26 : piu_zz_zprod_seg 512%nat (512%nat + 80%nat) 16%nat = ((if zz_in_Pn 512 593%nat then Z.of_nat 593%nat else 1%Z) * ((if zz_in_Pn 512 594%nat then Z.of_nat 594%nat else 1%Z) * ((if zz_in_Pn 512 595%nat then Z.of_nat 595%nat else 1%Z) * ((if zz_in_Pn 512 596%nat then Z.of_nat 596%nat else 1%Z) * ((if zz_in_Pn 512 597%nat then Z.of_nat 597%nat else 1%Z) * ((if zz_in_Pn 512 598%nat then Z.of_nat 598%nat else 1%Z) * ((if zz_in_Pn 512 599%nat then Z.of_nat 599%nat else 1%Z) * ((if zz_in_Pn 512 600%nat then Z.of_nat 600%nat else 1%Z) * ((if zz_in_Pn 512 601%nat then Z.of_nat 601%nat else 1%Z) * ((if zz_in_Pn 512 602%nat then Z.of_nat 602%nat else 1%Z) * ((if zz_in_Pn 512 603%nat then Z.of_nat 603%nat else 1%Z) * ((if zz_in_Pn 512 604%nat then Z.of_nat 604%nat else 1%Z) * ((if zz_in_Pn 512 605%nat then Z.of_nat 605%nat else 1%Z) * ((if zz_in_Pn 512 606%nat then Z.of_nat 606%nat else 1%Z) * ((if zz_in_Pn 512 607%nat then Z.of_nat 607%nat else 1%Z) * (if zz_in_Pn 512 608%nat then Z.of_nat 608%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L670-L690 (assert Hb27) *)
Lemma piu_zz_hb_512_27 : piu_zz_zprod_seg 512%nat (512%nat + 64%nat) 16%nat = ((if zz_in_Pn 512 577%nat then Z.of_nat 577%nat else 1%Z) * ((if zz_in_Pn 512 578%nat then Z.of_nat 578%nat else 1%Z) * ((if zz_in_Pn 512 579%nat then Z.of_nat 579%nat else 1%Z) * ((if zz_in_Pn 512 580%nat then Z.of_nat 580%nat else 1%Z) * ((if zz_in_Pn 512 581%nat then Z.of_nat 581%nat else 1%Z) * ((if zz_in_Pn 512 582%nat then Z.of_nat 582%nat else 1%Z) * ((if zz_in_Pn 512 583%nat then Z.of_nat 583%nat else 1%Z) * ((if zz_in_Pn 512 584%nat then Z.of_nat 584%nat else 1%Z) * ((if zz_in_Pn 512 585%nat then Z.of_nat 585%nat else 1%Z) * ((if zz_in_Pn 512 586%nat then Z.of_nat 586%nat else 1%Z) * ((if zz_in_Pn 512 587%nat then Z.of_nat 587%nat else 1%Z) * ((if zz_in_Pn 512 588%nat then Z.of_nat 588%nat else 1%Z) * ((if zz_in_Pn 512 589%nat then Z.of_nat 589%nat else 1%Z) * ((if zz_in_Pn 512 590%nat then Z.of_nat 590%nat else 1%Z) * ((if zz_in_Pn 512 591%nat then Z.of_nat 591%nat else 1%Z) * (if zz_in_Pn 512 592%nat then Z.of_nat 592%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L691-L711 (assert Hb28) *)
Lemma piu_zz_hb_512_28 : piu_zz_zprod_seg 512%nat (512%nat + 48%nat) 16%nat = ((if zz_in_Pn 512 561%nat then Z.of_nat 561%nat else 1%Z) * ((if zz_in_Pn 512 562%nat then Z.of_nat 562%nat else 1%Z) * ((if zz_in_Pn 512 563%nat then Z.of_nat 563%nat else 1%Z) * ((if zz_in_Pn 512 564%nat then Z.of_nat 564%nat else 1%Z) * ((if zz_in_Pn 512 565%nat then Z.of_nat 565%nat else 1%Z) * ((if zz_in_Pn 512 566%nat then Z.of_nat 566%nat else 1%Z) * ((if zz_in_Pn 512 567%nat then Z.of_nat 567%nat else 1%Z) * ((if zz_in_Pn 512 568%nat then Z.of_nat 568%nat else 1%Z) * ((if zz_in_Pn 512 569%nat then Z.of_nat 569%nat else 1%Z) * ((if zz_in_Pn 512 570%nat then Z.of_nat 570%nat else 1%Z) * ((if zz_in_Pn 512 571%nat then Z.of_nat 571%nat else 1%Z) * ((if zz_in_Pn 512 572%nat then Z.of_nat 572%nat else 1%Z) * ((if zz_in_Pn 512 573%nat then Z.of_nat 573%nat else 1%Z) * ((if zz_in_Pn 512 574%nat then Z.of_nat 574%nat else 1%Z) * ((if zz_in_Pn 512 575%nat then Z.of_nat 575%nat else 1%Z) * (if zz_in_Pn 512 576%nat then Z.of_nat 576%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L712-L732 (assert Hb29) *)
Lemma piu_zz_hb_512_29 : piu_zz_zprod_seg 512%nat (512%nat + 32%nat) 16%nat = ((if zz_in_Pn 512 545%nat then Z.of_nat 545%nat else 1%Z) * ((if zz_in_Pn 512 546%nat then Z.of_nat 546%nat else 1%Z) * ((if zz_in_Pn 512 547%nat then Z.of_nat 547%nat else 1%Z) * ((if zz_in_Pn 512 548%nat then Z.of_nat 548%nat else 1%Z) * ((if zz_in_Pn 512 549%nat then Z.of_nat 549%nat else 1%Z) * ((if zz_in_Pn 512 550%nat then Z.of_nat 550%nat else 1%Z) * ((if zz_in_Pn 512 551%nat then Z.of_nat 551%nat else 1%Z) * ((if zz_in_Pn 512 552%nat then Z.of_nat 552%nat else 1%Z) * ((if zz_in_Pn 512 553%nat then Z.of_nat 553%nat else 1%Z) * ((if zz_in_Pn 512 554%nat then Z.of_nat 554%nat else 1%Z) * ((if zz_in_Pn 512 555%nat then Z.of_nat 555%nat else 1%Z) * ((if zz_in_Pn 512 556%nat then Z.of_nat 556%nat else 1%Z) * ((if zz_in_Pn 512 557%nat then Z.of_nat 557%nat else 1%Z) * ((if zz_in_Pn 512 558%nat then Z.of_nat 558%nat else 1%Z) * ((if zz_in_Pn 512 559%nat then Z.of_nat 559%nat else 1%Z) * (if zz_in_Pn 512 560%nat then Z.of_nat 560%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L733-L753 (assert Hb30) *)
Lemma piu_zz_hb_512_30 : piu_zz_zprod_seg 512%nat (512%nat + 16%nat) 16%nat = ((if zz_in_Pn 512 529%nat then Z.of_nat 529%nat else 1%Z) * ((if zz_in_Pn 512 530%nat then Z.of_nat 530%nat else 1%Z) * ((if zz_in_Pn 512 531%nat then Z.of_nat 531%nat else 1%Z) * ((if zz_in_Pn 512 532%nat then Z.of_nat 532%nat else 1%Z) * ((if zz_in_Pn 512 533%nat then Z.of_nat 533%nat else 1%Z) * ((if zz_in_Pn 512 534%nat then Z.of_nat 534%nat else 1%Z) * ((if zz_in_Pn 512 535%nat then Z.of_nat 535%nat else 1%Z) * ((if zz_in_Pn 512 536%nat then Z.of_nat 536%nat else 1%Z) * ((if zz_in_Pn 512 537%nat then Z.of_nat 537%nat else 1%Z) * ((if zz_in_Pn 512 538%nat then Z.of_nat 538%nat else 1%Z) * ((if zz_in_Pn 512 539%nat then Z.of_nat 539%nat else 1%Z) * ((if zz_in_Pn 512 540%nat then Z.of_nat 540%nat else 1%Z) * ((if zz_in_Pn 512 541%nat then Z.of_nat 541%nat else 1%Z) * ((if zz_in_Pn 512 542%nat then Z.of_nat 542%nat else 1%Z) * ((if zz_in_Pn 512 543%nat then Z.of_nat 543%nat else 1%Z) * (if zz_in_Pn 512 544%nat then Z.of_nat 544%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.

(* src piu_zz_tau_enclosure.v L754-L774 (assert Hb31) *)
Lemma piu_zz_hb_512_31 : piu_zz_zprod_seg 512%nat 512%nat 16%nat = ((if zz_in_Pn 512 513%nat then Z.of_nat 513%nat else 1%Z) * ((if zz_in_Pn 512 514%nat then Z.of_nat 514%nat else 1%Z) * ((if zz_in_Pn 512 515%nat then Z.of_nat 515%nat else 1%Z) * ((if zz_in_Pn 512 516%nat then Z.of_nat 516%nat else 1%Z) * ((if zz_in_Pn 512 517%nat then Z.of_nat 517%nat else 1%Z) * ((if zz_in_Pn 512 518%nat then Z.of_nat 518%nat else 1%Z) * ((if zz_in_Pn 512 519%nat then Z.of_nat 519%nat else 1%Z) * ((if zz_in_Pn 512 520%nat then Z.of_nat 520%nat else 1%Z) * ((if zz_in_Pn 512 521%nat then Z.of_nat 521%nat else 1%Z) * ((if zz_in_Pn 512 522%nat then Z.of_nat 522%nat else 1%Z) * ((if zz_in_Pn 512 523%nat then Z.of_nat 523%nat else 1%Z) * ((if zz_in_Pn 512 524%nat then Z.of_nat 524%nat else 1%Z) * ((if zz_in_Pn 512 525%nat then Z.of_nat 525%nat else 1%Z) * ((if zz_in_Pn 512 526%nat then Z.of_nat 526%nat else 1%Z) * ((if zz_in_Pn 512 527%nat then Z.of_nat 527%nat else 1%Z) * (if zz_in_Pn 512 528%nat then Z.of_nat 528%nat else 1%Z)))))))))))))))).
Proof.
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
Qed.
