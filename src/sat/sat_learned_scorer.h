/*++
Copyright (c) 2026 Z3 Contributors

Module Name:

    sat_learned_scorer.h

Abstract:

    Tiny linear model that scores SAT variables from an 8-feature vector.
    Trains online via Adam optimizer using conflict reward signals.

    Inference: score = dot(features, weights)  (~3ns for 8 FMAs, auto-vectorized)
    Training:  Adam update on each feature weight after every conflict.

    The model starts as "pure Adam momentum" (weight[0]=1, rest=0) and learns
    to incorporate other features from conflict feedback.

Author:

    Z3 Contributors

--*/
#pragma once

#include <cmath>
#include <cstring>

namespace sat {

class learned_scorer {
    static constexpr unsigned N_FEATURES = 8;

    // Linear model weights
    double m_weights[N_FEATURES];

    // Adam optimizer state per weight
    double m_w_m1[N_FEATURES];  // first moment  (EMA of gradient)
    double m_w_m2[N_FEATURES];  // second moment (EMA of squared gradient)
    uint64_t m_train_step;

public:
    learned_scorer() : m_train_step(0) {
        std::memset(m_weights, 0, sizeof(m_weights));
        m_weights[0] = 1.0;  // bootstrap: pure Adam momentum
        std::memset(m_w_m1, 0, sizeof(m_w_m1));
        std::memset(m_w_m2, 0, sizeof(m_w_m2));
    }

    // Inference: dot product of feature vector and weights.
    // The loop over 8 doubles is auto-vectorized by clang/gcc.
    double score(const double* features) const {
        double s = 0.0;
        for (unsigned i = 0; i < N_FEATURES; ++i)
            s += features[i] * m_weights[i];
        return s;
    }

    // Online training step: Adam update on all weights.
    //   reward = 1.0/max(glue, 1) for variables bumped in a conflict
    //   gradient = -reward * features  (we want to increase score for
    //   variables that participate in low-glue conflicts)
    void train(const double* features, double reward) {
        ++m_train_step;
        for (unsigned i = 0; i < N_FEATURES; ++i) {
            double g = -reward * features[i];
            m_w_m1[i] = 0.9  * m_w_m1[i] + 0.1   * g;
            m_w_m2[i] = 0.999 * m_w_m2[i] + 0.001 * g * g;
            m_weights[i] -= 0.001 * m_w_m1[i] / (std::sqrt(m_w_m2[i]) + 1e-8);
        }
    }

    uint64_t train_steps() const { return m_train_step; }
    double weight(unsigned i) const { return i < N_FEATURES ? m_weights[i] : 0.0; }
};

} // namespace sat
