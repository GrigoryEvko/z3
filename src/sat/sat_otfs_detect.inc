                // OTFS: On-the-fly strengthening (CaDiCaL-style).
                // After resolving against this clause, check if the resolvent is
                // smaller than the antecedent. If so, the pivot literal is redundant
                // in the antecedent and can be removed.
                // resolvent_size = num_marks (conflict-level) + lemma.size()-1 (below-level)
                // antecedent_size = c.size()
                // We only apply to the non-initial clauses (consequent != null_literal means
                // this is a reason clause, not the conflict clause itself) and non-binary clauses.
                // Skip when DRAT proofs are enabled (proof tracking for OTFS is complex).
                if (m_config.m_otfs && !m_config.m_drat &&
                    consequent != null_literal && sz > 2) {
                    unsigned resolvent_size = num_marks + (m_lemma.size() - 1);
                    if (resolvent_size < sz) {
                        on_the_fly_strengthen(c, consequent, js.get_clause_offset());
                    }
                }
