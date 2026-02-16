/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    ema.h

Abstract:

    Exponential moving average with ADAM-style bias correction
    (Kingma & Ba, ICLR 2015). The biased EMA is divided by
    (1 - beta^t) where beta = 1 - alpha, giving an unbiased
    estimate that converges quickly during early updates.

Author:

    Nikolaj Bjorner (nbjorner) 2018-05-03

Revision History:

--*/
#pragma once

class ema {
    double m_alpha  = 0;    // smoothing rate
    double m_biased = 0;    // biased moving average
    double m_exp    = 1.0;  // tracks (1 - alpha)^t = beta^t
    double m_value  = 0;    // bias-corrected value
 public:
    ema() {}

    ema(double alpha):
        m_alpha(alpha), m_biased(0), m_exp(1.0), m_value(0) {}

    void set_alpha(double alpha) {
        m_alpha = alpha;
    }

    operator double () const { return m_value; }

    void update(double x) {
        m_biased += m_alpha * (x - m_biased);
        m_exp *= (1.0 - m_alpha);
        double div = 1.0 - m_exp;
        if (div > 0)
            m_value = m_biased / div;
        else
            m_value = x;
    }

    void set(double x) {
        m_value = x;
    }
};

