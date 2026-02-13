    /**
       \brief On-the-fly strengthening (OTFS): remove pivot from clause c
       during conflict analysis. When the resolvent is smaller than the
       antecedent clause c, the antecedent can be strengthened by removing
       the resolved-away pivot literal.
       Based on CaDiCaL's on_the_fly_strengthen (analyze.cpp:770-865).
    */
    void solver::on_the_fly_strengthen(clause& c, literal pivot, clause_offset cls_off) {
        SASSERT(c.size() > 2);
        SASSERT(c.contains(pivot));

        unsigned old_sz = c.size();

        // Find pivot position in clause.
        unsigned pivot_pos = UINT_MAX;
        for (unsigned i = 0; i < old_sz; ++i) {
            if (c[i] == pivot) {
                pivot_pos = i;
                break;
            }
        }
        SASSERT(pivot_pos != UINT_MAX);

        bool pivot_was_watched = (pivot_pos == 0 || pivot_pos == 1);

        if (old_sz == 3) {
            // Shrinking ternary to binary: collect remaining literals.
            literal remaining[2];
            unsigned j = 0;
            for (unsigned i = 0; i < 3; ++i) {
                if (i != pivot_pos)
                    remaining[j++] = c[i];
            }
            SASSERT(j == 2);

            // Remove clause watches for both watched literals.
            erase_clause_watch(get_wlist(~c[0]), cls_off);
            erase_clause_watch(get_wlist(~c[1]), cls_off);

            // Add binary watches.
            bool learned = c.is_learned();
            get_bin_wlist(~remaining[0]).push_back(watched(remaining[1], learned));
            get_bin_wlist(~remaining[1]).push_back(watched(remaining[0], learned));

            // Update justification: propagated literal now justified by binary clause.
            literal propagated = null_literal;
            for (unsigned i = 0; i < 2; ++i) {
                if (value(remaining[i]) == l_true) {
                    propagated = remaining[i];
                    break;
                }
            }
            if (propagated != null_literal) {
                literal other = (remaining[0] == propagated) ? remaining[1] : remaining[0];
                m_justification[propagated.var()] = justification(lvl(propagated), ~other);
            }

            c.set_removed(true);
            m_stats.m_otfs_strengthened++;
            return;
        }

        // General case: clause size > 3, shrinking by one literal.
        if (pivot_was_watched) {
            unsigned other_watched_pos = (pivot_pos == 0) ? 1 : 0;
            literal other_watched = c[other_watched_pos];

            // Remove watch from ~pivot's list.
            erase_clause_watch(get_wlist(~pivot), cls_off);

            // Pick highest-level non-watched literal as replacement.
            unsigned best_pos = 2;
            unsigned best_lvl = lvl(c[2]);
            for (unsigned i = 3; i < old_sz; ++i) {
                unsigned l = lvl(c[i]);
                if (l > best_lvl) {
                    best_lvl = l;
                    best_pos = i;
                }
            }

            literal replacement = c[best_pos];
            c[pivot_pos] = replacement;
            if (best_pos != old_sz - 1)
                c[best_pos] = c[old_sz - 1];
            c.shrink(old_sz - 1);

            // Add watch for ~replacement.
            literal block_lit = c[c.size() >> 1];
            get_wlist(~replacement).push_back(watched(block_lit, cls_off));

            // Update blocked literal in the other watch.
            watch_list& owlist = get_wlist(~other_watched);
            for (auto& w : owlist) {
                if (w.is_clause() && w.get_clause_offset() == cls_off) {
                    w.set_blocked_literal(block_lit);
                    break;
                }
            }
        }
        else {
            // Pivot not watched (position >= 2): swap with last and shrink.
            if (pivot_pos != old_sz - 1)
                std::swap(c[pivot_pos], c[old_sz - 1]);
            c.shrink(old_sz - 1);

            // Update blocked literal in both watch lists.
            literal new_block = c[c.size() >> 1];
            for (unsigned w = 0; w < 2; ++w) {
                watch_list& wl = get_wlist(~c[w]);
                for (auto& we : wl) {
                    if (we.is_clause() && we.get_clause_offset() == cls_off) {
                        we.set_blocked_literal(new_block);
                        break;
                    }
                }
            }
        }

        c.mark_used();
        m_stats.m_otfs_strengthened++;
    }

