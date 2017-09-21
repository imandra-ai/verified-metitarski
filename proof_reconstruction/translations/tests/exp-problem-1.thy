theory "exp-problem-1"
imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).((((0 <= X) \<and> (X <= 1)) --> ((exp(X) - (1 + X)) <= (X ^ 2 * exp(X)))))"
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real
    have ff1: "(1 + rr) * (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) < 21743271936 + rr * (rr * - 21743271936) \<or> 21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> 0 \<or> (21743271936 + rr * (rr * - 21743271936)) / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<le> 1 + rr"
      using leq_left_divide_mul_pos by blast (* 20 ms *)
    have ff2: "1 + rr < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) * (1 + rr * (rr * - 1)) \<or> 1 + rr * (rr * - 1) \<le> 0 \<or> 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<le> (1 + rr) / (1 + rr * (rr * - 1))"
      using leq_right_divide_mul_pos by blast (* 8 ms *)
    have ff3: "\<And>r ra. \<not> lgen False (exp ra) r \<or> exp ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. 3 < ra \<or> \<not> lgen False (21743271936 / (- (ra ^ 3) + 12 * ra\<^sup>2 - 96 * ra + 384) ^ 4) r \<or> lgen False (exp ra) r"
      using exp_upper_bound_case_5 by auto (* failed *)
    then have "\<And>r ra. 3 < ra \<or> \<not> lgen False (21743271936 / (- (ra ^ 3) + 12 * ra\<^sup>2 - 96 * ra + 384) ^ 4) r \<or> exp ra \<le> r"
      using ff3 by blast (* 8 ms *)
    then have "\<And>r ra. 3 < (ra::real) \<or> r < 21743271936 / (21743271936 + ra * (- 21743271936 + ra * (10871635968 + ra * (- 3623878656 + ra * (891813888 + ra * (- 169869312 + ra * (25657344 + ra * (- 3096576 + ra * (297216 + ra * (- 22272 + ra * (1248 + ra * (- 48 + ra)))))))))))) \<or> exp ra \<le> r"
      by mt_arith_rule (* failed *)
    then have ff4: "(1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<or> 3 < rr \<or> exp rr \<le> (1 + rr) / (1 + rr * (rr * - 1))"
      by blast (* 4 ms *)
    have ff5: "(1 + rr) * (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) < 2304 + rr * (rr * - 2304) \<or> 2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> 0 \<or> (2304 + rr * (rr * - 2304)) / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<le> 1 + rr"
      using leq_left_divide_mul_pos by blast (* 4 ms *)
    have ff6: "1 + rr < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) * (1 + rr * (rr * - 1)) \<or> 1 + rr * (rr * - 1) \<le> 0 \<or> 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<le> (1 + rr) / (1 + rr * (rr * - 1))"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff7: "\<And>r ra. \<not> lgen False (exp ra) r \<or> exp ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. 0 < ra \<or> \<not> lgen False (2304 / (- (ra ^ 3) + 6 * ra\<^sup>2 - 24 * ra + 48)\<^sup>2) r \<or> lgen False (exp ra) r"
      using exp_upper_bound_case_3 by auto (* failed *)
    then have "\<And>r ra. 0 < ra \<or> \<not> lgen False (2304 / (- (ra ^ 3) + 6 * ra\<^sup>2 - 24 * ra + 48)\<^sup>2) r \<or> exp ra \<le> r"
      using ff7 by blast (* 0.0 ms *)
    then have "\<And>r ra. (0::real) < ra \<or> r < 2304 / (2304 + ra * (- 2304 + ra * (1152 + ra * (- 384 + ra * (84 + ra * (- 12 + ra)))))) \<or> exp ra \<le> r"
      by mt_arith_rule (* failed *)
    then have ff8: "(1 + rr) / (1 + rr * (rr * - 1)) < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<or> 0 < rr \<or> exp rr \<le> (1 + rr) / (1 + rr * (rr * - 1))"
      by blast (* 4 ms *)
    have "\<not> - 21743271936 < rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<or> \<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936"
      by force (* 432 ms *)
    moreover
    { assume "\<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936"
      then have "\<not> rr * (rr * (- 10871635968 + rr * (- 7247757312 + rr * (2732064768 + rr * (- 721944576 + rr * (144211968 + rr * (- 22560768 + rr * (2799360 + rr * (- 274944 + rr * (21024 + rr * (- 1200 + rr * (47 + rr * - 1)))))))))))) \<le> 0 \<and> \<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936 \<or> \<not> 0 < rr * (rr * (- 10871635968 + rr * (- 7247757312 + rr * (2732064768 + rr * (- 721944576 + rr * (144211968 + rr * (- 22560768 + rr * (2799360 + rr * (- 274944 + rr * (21024 + rr * (- 1200 + rr * (47 + rr * - 1)))))))))))) \<and> \<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936"
        by simp (* 64 ms *)
      moreover
      { assume "\<not> 0 < rr * (rr * (- 10871635968 + rr * (- 7247757312 + rr * (2732064768 + rr * (- 721944576 + rr * (144211968 + rr * (- 22560768 + rr * (2799360 + rr * (- 274944 + rr * (21024 + rr * (- 1200 + rr * (47 + rr * - 1)))))))))))) \<and> \<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936"
        then have "\<not> (1 + rr) * (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) < 21743271936 + rr * (rr * - 21743271936) \<and> \<not> 21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> 0"
          by mt_arith_rule (* 1.1 s *)
        then have "\<not> 1 + rr < (21743271936 + rr * (rr * - 21743271936)) / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))))"
          using ff1 by simp (* 536 ms *)
        then have "- 1 < rr * (rr * - 1) \<longrightarrow> \<not> 1 + rr < (21743271936 + rr * (rr * - 21743271936)) / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> rr * (rr * - 1) \<le> - 1"
          by fastforce (* 12 ms *)
        moreover
        { assume "\<not> 1 + rr < (21743271936 + rr * (rr * - 21743271936)) / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> rr * (rr * - 1) \<le> - 1"
          then have "\<not> 1 + rr < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) * (1 + rr * (rr * - 1)) \<and> \<not> 1 + rr * (rr * - 1) \<le> 0"
            by mt_arith_rule (* 2.1 s *)
          then have "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))))"
            using ff2 by simp (* 128 ms *)
          then have "rr \<le> 3 \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> 3 < rr"
            by force (* 12 ms *)
          moreover
          { assume "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> 3 < rr"
            then have "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 3 < rr \<or> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> 3 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              by auto (* 20 ms *)
            moreover
            { assume "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < 21743271936 / (21743271936 + rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))) \<and> \<not> 3 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              then have "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
                using ff4 by fastforce (* 24 ms *) }
            moreover
            { assume "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 3 < rr"
              then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 0 < rr \<or> \<not> - 1 < rr * (rr * - 1)"
                by sos (* 24 ms *) }
            ultimately have "- 1 < rr * (rr * - 1) \<and> 0 < rr \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              by metis (* 44 ms *) }
          moreover
          { assume "\<not> rr \<le> 3"
            then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 0 < rr \<or> \<not> - 1 < rr * (rr * - 1)"
              by sos (* 8 ms *) }
          ultimately have "- 1 < rr * (rr * - 1) \<and> 0 < rr \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
            by metis (* 60 ms *) }
        ultimately have "- 1 < rr * (rr * - 1) \<and> 0 < rr \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
          by metis (* 40 ms *) }
      moreover
      { assume "\<not> rr * (rr * (- 10871635968 + rr * (- 7247757312 + rr * (2732064768 + rr * (- 721944576 + rr * (144211968 + rr * (- 22560768 + rr * (2799360 + rr * (- 274944 + rr * (21024 + rr * (- 1200 + rr * (47 + rr * - 1)))))))))))) \<le> 0 \<and> \<not> rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr))))))))))) \<le> - 21743271936"
        then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 0 < rr \<or> \<not> - 1 < rr * (rr * - 1)"
          sorry (*by sos*) (* > 5.0 s, timed out *) }
      ultimately have "- 1 < rr * (rr * - 1) \<and> 0 < rr \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
        by metis (* 176 ms *) }
    moreover
    { assume "\<not> - 21743271936 < rr * (- 21743271936 + rr * (10871635968 + rr * (- 3623878656 + rr * (891813888 + rr * (- 169869312 + rr * (25657344 + rr * (- 3096576 + rr * (297216 + rr * (- 22272 + rr * (1248 + rr * (- 48 + rr)))))))))))"
      then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 0 < rr \<or> \<not> - 1 < rr * (rr * - 1)"
        sorry (*by sos*) (* > 5.0 s, timed out *) }
    ultimately have "- 1 < rr * (rr * - 1) \<and> 0 < rr \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
      by metis (* 88 ms *)
    moreover
    { assume "\<not> 0 < rr"
      then have "\<not> - 2304 < rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<and> \<not> 0 < rr \<or> \<not> 0 < rr \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304"
        by auto (* 56 ms *)
      moreover
      { assume "\<not> 0 < rr \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304"
        then have "\<not> 0 < rr \<and> \<not> rr * (rr * (- 1152 + rr * (- 768 + rr * (300 + rr * (- 72 + rr * (11 + rr * - 1)))))) \<le> 0 \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304 \<or> \<not> 0 < rr * (rr * (- 1152 + rr * (- 768 + rr * (300 + rr * (- 72 + rr * (11 + rr * - 1)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304"
          by auto (* 52 ms *)
        moreover
        { assume "\<not> 0 < rr * (rr * (- 1152 + rr * (- 768 + rr * (300 + rr * (- 72 + rr * (11 + rr * - 1)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304"
          then have "\<not> (1 + rr) * (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) < 2304 + rr * (rr * - 2304) \<and> \<not> 0 < rr \<and> \<not> 2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> 0"
            by mt_arith_rule (* 196 ms *)
          then have "\<not> 1 + rr < (2304 + rr * (rr * - 2304)) / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr"
            using ff5 by auto (* 64 ms *)
          then have "\<not> 1 + rr < (2304 + rr * (rr * - 2304)) / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1 \<or> \<not> - 1 < rr * (rr * - 1) \<and> \<not> 0 < rr"
            by auto (* 16 ms *)
          moreover
          { assume "\<not> 1 + rr < (2304 + rr * (rr * - 2304)) / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
            then have "\<not> 1 + rr < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) * (1 + rr * (rr * - 1)) \<and> \<not> 0 < rr \<and> \<not> 1 + rr * (rr * - 1) \<le> 0"
              by mt_arith_rule (* 464 ms *)
            then have "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr"
              using ff6 by auto (* 36 ms *)
            then have "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 0 < rr \<or> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              by auto (* 24 ms *)
            moreover
            { assume "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < 2304 / (2304 + rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr)))))) \<and> \<not> 0 < rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              then have "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
                using ff8 by simp (* 32 ms *) }
            ultimately have "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 0 < rr \<or> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
              by metis (* 44 ms *) }
          ultimately have "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 0 < rr \<or> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
            by metis (* 48 ms *)
          moreover
          { assume "\<not> - 1 < rr * (rr * - 1) \<and> \<not> 0 < rr"
            then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> - 1 < rr * (rr * - 1)"
              by sos (* 24 ms *) }
          ultimately have "- 1 < rr * (rr * - 1) \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
            by metis (* 20 ms *) }
        moreover
        { assume "\<not> 0 < rr \<and> \<not> rr * (rr * (- 1152 + rr * (- 768 + rr * (300 + rr * (- 72 + rr * (11 + rr * - 1)))))) \<le> 0 \<and> \<not> rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<le> - 2304"
          then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> - 1 < rr * (rr * - 1)"
            sorry (*by sos*) (* > 5.0 s, timed out *) }
        ultimately have "- 1 < rr * (rr * - 1) \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
          by metis (* 100 ms *) }
      moreover
      { assume "\<not> - 2304 < rr * (- 2304 + rr * (1152 + rr * (- 384 + rr * (84 + rr * (- 12 + rr))))) \<and> \<not> 0 < rr"
        then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> - 1 < rr * (rr * - 1)"
          sorry (*by sos*) (* > 5.0 s, timed out *) }
      ultimately have "- 1 < rr * (rr * - 1) \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
        by metis (* 44 ms *) }
    ultimately have "- 1 < rr * (rr * - 1) \<and> rr \<le> 1 \<and> 0 \<le> rr \<longrightarrow> \<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
      by metis (* 20 ms *)
    moreover
    { assume "\<not> (1 + rr) / (1 + rr * (rr * - 1)) < exp rr \<and> \<not> rr * (rr * - 1) \<le> - 1"
      then have "\<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
        by mt_arith_rule (* 36 ms *) }
    moreover
    { assume "\<not> - 1 < rr * (rr * - 1)"
      then have "\<not> - 1 < rr * (rr * - 1) \<and> \<not> - 1 \<le> rr \<or> \<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1)"
        by simp (* 12 ms *)
      moreover
      { assume "\<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1)"
        then have "\<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1) \<and> \<not> rr * rr \<le> 1 \<or> \<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1) \<and> \<not> 1 < rr * rr"
          by simp (* 8 ms *)
        moreover
        { assume "\<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1) \<and> \<not> 1 < rr * rr"
          then have "\<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
            by mt_arith_rule (* failed *) }
        moreover
        { assume "\<not> rr < - 1 \<and> \<not> - 1 < rr * (rr * - 1) \<and> \<not> rr * rr \<le> 1"
          then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
            by sos (* 56 ms *) }
        ultimately have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
          by metis (* 48 ms *) }
      moreover
      { assume "\<not> - 1 < rr * (rr * - 1) \<and> \<not> - 1 \<le> rr"
        then have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
          by sos (* 16 ms *) }
      ultimately have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
        by metis (* 40 ms *) }
    ultimately have "\<not> 0 \<le> rr \<or> \<not> rr \<le> 1 \<or> \<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
      by metis (* 56 ms *)
    moreover
    { assume "\<not> 1 + rr < exp rr * (1 + rr * (rr * - 1))"
      then have "\<not> rr\<^sup>2 * exp rr < exp rr - (1 + rr)"
        by mt_arith_rule (* 24 ms *)
      then have "\<not> rr\<^sup>2 * exp rr < exp rr - (1 + rr) \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
        by metis (* 8 ms *) }
    moreover
    { assume "\<not> rr \<le> 1"
      then have "\<not> rr\<^sup>2 * exp rr < exp rr - (1 + rr) \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
        by metis (* 8 ms *) }
    moreover
    { assume "\<not> 0 \<le> rr"
      then have "\<not> rr\<^sup>2 * exp rr < exp rr - (1 + rr) \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
        by metis (* 12 ms *) }
    ultimately have "\<not> rr\<^sup>2 * exp rr < exp rr - (1 + rr) \<or> \<not> 0 \<le> rr \<or> \<not> rr \<le> 1"
      by metis (* 24 ms *) }
  then have "\<forall>r. \<not> (r::real)\<^sup>2 * exp r < exp r - (1 + r) \<or> \<not> r \<le> 1 \<or> \<not> 0 \<le> r"
    by meson (* 4 ms *)
  then show ?thesis
    by auto (* 8 ms *)
qed
  
end  