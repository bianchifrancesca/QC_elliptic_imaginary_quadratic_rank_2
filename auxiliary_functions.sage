r"""
Auxiliary functions. Some of these functions are from:

https://github.com/bianchifrancesca/quadratic_chabauty

These functions were also used for some of the computations of
[BBBM19].

REFERENCES:

- [BBBM19] \J. S. Balakrishnan, A. Besser, F. Bianchi, J. S. Mueller,
  "Explicit quadratic Chabauty over number fields". To appear in
  "Isr. J. Math.".
"""

import itertools


def coleman_integrals_on_basis(H, P, Q, inverse_frob, forms, algorithm=None):
    r"""
    Compute the Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.
    The only difference with the built-in function `coleman_integrals_on_basis`
    is that we input the Frobenius data `(inverse_frob, forms)`.

    INPUT:

    - ``H`` -- a hyperelliptic curve over a `p`-adic field `K`.

    - ``P`` -- a point on `H`.

    - ``Q`` -- a point on `H`.

    - ``inverse_frob`` -- `(M_frob^T-1)^(-1)` where `M_frob` is the matrix of Frobenius
      on Monsky-Washnitzer cohomology, with respect to the basis `(dx/2y, x dx/2y, ...x^{d-2} dx/2y)`
      and with coefficients in `K`.

    - ``forms`` -- list of differentials `\{f_i\}` such that
      `\phi^* (x^i dx/2y) = df_i + M_frob[i]*vec(dx/2y, ..., x^{d-2} dx/2y)`;
      the coefficients of the `f_i` should be in `K`.

    - ``algorithm`` (optional) --  None (uses Frobenius) or teichmuller
      (uses Teichmuller points).

    OUTPUT:

    The Coleman integrals `\{\int_P^Q x^i dx/2y \}_{i=0}^{2g-1}`.

    EXAMPLES:

    This example illustrates how to compute the data `(inverse_frob,forms)` for `H`::

        sage: import sage.schemes.hyperelliptic_curves.monsky_washnitzer as monsky_washnitzer
        sage: K = H.base_ring()
        sage: M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H)
        sage: forms = [form.change_ring(K) for form in forms]
        sage: M_sys = matrix(K, M_frob).transpose() - 1
        sage: inverse_frob = M_sys**(-1)
    """
    K = H.base_ring()
    p = K.prime()
    prec = K.precision_cap()
    g = H.genus()
    dim = 2*g
    V = VectorSpace(K, dim)
    #if P or Q is Weierstrass, use the Frobenius algorithm
    if H.is_weierstrass(P):
        if H.is_weierstrass(Q):
            return V(0)
        else:
            PP = None
            QQ = Q
            TP = None
            TQ = H.frobenius(Q)
    elif H.is_weierstrass(Q):
        PP = P
        QQ = None
        TQ = None
        TP = H.frobenius(P)
    elif H.is_same_disc(P, Q):
        return H.tiny_integrals_on_basis(P, Q)
    elif algorithm == 'teichmuller':
        PP = TP = H.teichmuller(P)
        QQ = TQ = H.teichmuller(Q)
        evalP, evalQ = TP, TQ
    else:
        TP = H.frobenius(P)
        TQ = H.frobenius(Q)
        PP, QQ = P, Q
    if TP is None:
        P_to_TP = V(0)
    else:
        if TP is not None:
            TPv = (TP[0]**g/TP[1]).valuation()
            xTPv = TP[0].valuation()
        else:
            xTPv = TPv = +Infinity
        if TQ is not None:
            TQv = (TQ[0]**g/TQ[1]).valuation()
            xTQv = TQ[0].valuation()
        else:
            xTQv = TQv = +Infinity
        offset = (2*g-1)*max(TPv, TQv)
        if offset == +Infinity:
            offset = (2*g-1)*min(TPv,TQv)
        if (offset > prec and (xTPv < 0 or xTQv < 0) and (H.residue_disc(P) == H.change_ring(GF(p))(0, 1, 0) or H.residue_disc(Q) == H.change_ring(GF(p))(0, 1, 0))):
            newprec = offset + prec
            K = pAdicField(p,newprec)
            A = PolynomialRing(RationalField(),'x')
            f = A(H.hyperelliptic_polynomials()[0])
            from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
            H = HyperellipticCurve(f).change_ring(K)
            xP = P[0]
            xPv = xP.valuation()
            xPnew = K(sum(c * p**(xPv + i) for i, c in enumerate(xP.expansion())))
            PP = P = H.lift_x(xPnew)
            TP = H.frobenius(P)
            xQ = Q[0]
            xQv = xQ.valuation()
            xQnew = K(sum(c * p**(xQv + i) for i, c in enumerate(xQ.expansion())))
            QQ = Q = H.lift_x(xQnew)
            TQ = H.frobenius(Q)
            V = VectorSpace(K,dim)
        P_to_TP = V(H.tiny_integrals_on_basis(P, TP))
    if TQ is None:
        TQ_to_Q = V(0)
    else:
        TQ_to_Q = V(H.tiny_integrals_on_basis(TQ, Q))
    if PP is None:
        L = [-f(QQ[0], QQ[1]) for f in forms]  ##changed
    elif QQ is None:
        L = [f(PP[0], PP[1]) for f in forms]
    else:
        L = [f(PP[0], PP[1]) - f(QQ[0], QQ[1]) for f in forms]
    b = V(L)
    if PP is None:
        b -= TQ_to_Q
    elif QQ is None:
        b -= P_to_TP
    elif algorithm != 'teichmuller':
        b -= P_to_TP + TQ_to_Q
    #M_sys = matrix(K, M_frob).transpose() - 1
    TP_to_TQ = inverse_frob * b
    if algorithm == 'teichmuller':
        return P_to_TP + TP_to_TQ + TQ_to_Q
    else:
        return TP_to_TQ


def Q_lift(CK, Q, p):
    r"""
    Compute the Teichmueller point lifting a given point over `GF(p)`.

    INPUT:

    - ``CK`` -- a hyperelliptic curve over `\QQ_p`.

    - ``Q`` -- a point in `CK(GF(p))`.

    - ``p`` -- the prime of the first two inputs.

    OUTPUT: The point on `CK` lifting `Q` and fixed by Frobenius.
    """
    xQ = Integers()(Q[0])
    yQ = Integers()(Q[1])
    if yQ == 0:
        r = CK.hyperelliptic_polynomials()[0].roots()
        Q_lift = CK(exists(r, lambda a : (Integers()(a[0])-xQ) % p == 0)[1][0],0)
    else:
        K = CK.base_ring()
        xQ = K.teichmuller(K(xQ))
        lifts = CK.lift_x(xQ, all=True)
        for i in range(len(lifts)):
            if (Integers()(lifts[i][1])-yQ) % p == 0:
                Q_lift = lifts[i]
    return Q_lift


def embeddings(K, p, prec):
    """r
    Compute the embedding(s) of `K` in the completions of `K` at
    the primes above `p`. This is taken from the code used for [BcL+16].

    INPUT:

    - ``K`` -- a quadratic field.

    - ``p`` -- a prime.

    - ``prec`` -- the `p`-adic precision.

    OUTPUT:
    A list of embeddings of `K` in `\QQ_p` if `p` splits in `K`;
    an embedding of `K =\QQ(\sqrt(D))` in `\QQ_p(\sqrt(D))` otherwise.

    REFERENCES:

    - [BcL+16] \J. S. Balakrishnan, M. Ciperiani, J. Lang, B. Mirza, and R. Newton, "Shadow
      lines in the arithmetic of elliptic curves". In" Directions in number theory, volume 3".
    """
    Q = pAdicField(p,prec)
    OK = K.maximal_order()
    pOK = factor(p*OK)
    if (len(pOK) == 2 and pOK[0][1] == 1):
        R = Q['x']
        r1, r2 = R(K.defining_polynomial()).roots()
        psi1 = K.hom([r1[0]])
        psi2 = K.hom([r2[0]])
        return [psi1, psi2]
    else:
        F = Q.extension(K.defining_polynomial(),names='a')
        a = F.gen()
        psi = self._psis = [K.hom([a])]
        return psi


def bernardi_sigma_function(E, prec=20):
    r"""
    Return the sigma function of Bernardi in terms of `z = log(t)`.
    This is an adaptation of the code built in sage. The difference is that we input
    the curve instead of the `L`-function and that we are adding `r` to `xofF`.

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`.

    - ``prec`` -- power series precision.

    OUTPUT: A power series in `z` with coefficients in \QQ approximating the sigma function
    of Bernardi.

    .. NOTE::

        This will converge on some `p`-adic neighbourhood of the identity on `E`
        for a prime `p` of good reduction.
    """
    Eh = E.formal()
    lo = Eh.log(prec + 5)
    F = lo.reverse()

    S = LaurentSeriesRing(QQ,'z',default_prec = prec)
    z = S.gen()
    F = F(z)
    xofF = Eh.x(prec + 2)(F)
    r =  ( E.a1()**2 + 4*E.a2() ) / ZZ(12)
    xofF = xofF + r
    g = (1/z**2 - xofF ).power_series()
    h = g.integral().integral()
    sigma_of_z = z.power_series() * h.exp()

    return sigma_of_z


def height_bernardi(P, p, prec):
    """r
    Return the `p`-adic height of Bernardi at `P`.

    INPUT:

    - ``P`` -- a point on an elliptic curve `E` over `\QQ`.

    - ``p`` -- an odd prime of good reduction for `E`.

    - ``prec`` -- integer. The precision of the computation.

    OUTPUT:
    A `p`-adic number; the Bernardi `p`-adic height of `P`.
    """
    E = P.scheme()
    tam = E.tamagawa_numbers()
    tam.append(E.Np(p))
    m = lcm(tam)
    Q = m*P
    dQ = ZZ(Q[0].denominator().sqrt())
    sigma = bernardi_sigma_function(E,prec=prec+5)
    sigma = sigma(E.formal().log(prec+5))
    sigmaQ = Qp(p, prec)(sigma(-Qp(p,prec+5)(Q[0]/Q[1])))
    return (-2*log(sigmaQ/dQ))/m^2


############## SOLVERS OF SYSTEMS OF MULTIVARIABLE p-ADIC POLYNOMIALS ##############


def hensel_lift_n(flist, p, prec):
    r"""
    Multivariable Hensel lifter for roots that are simple
    modulo `p`.
    This is essentially the code from [S15] with some minor
    modifications.

    INPUT:

    - ``flist`` -- A list of `n` polynomials in `n` variables
      over a `p`-adic field. Each polynomial should have coefficients in
      `\ZZ_p` and be normalised so that the minimal valaution of its
      coefficients is `0`.

    - ``p`` -- the prime number of the first input item.

    - ``prec`` -- `p`-adic precision. In order for the output to be given
      modulo `p^{prec}`, the coefficients of the polynomials in `flist`
      should be known at least modulo `p^{prec}`.

    OUTPUT:

    A tuple consisting of:

    - A list `L` of common roots in `Qp(p, prec)` of the polynomials in `flist`
      (each root is returned as an `(n x 1)`-matrix, where the `i`-th row 
      corresponds to the `i`-th variable).
      Each root in this list lift uniquely to a root in `\QQ_p`.

    - An integer: the number of roots modulo `p` of `flist` for which the
      determinant of the Jacobian matrix vanishes modulo `p`. If this is zero,
      then the `L` contains all the roots of `flist`.

    EXAMPLES:

    An example with no double roots modulo `p`::

        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s + t - 2*s*t
        sage: f2 = s - t
        sage: a, b = hensel_lift_n([f1, f2], 5, 10)
        sage: print a
        [[0]
        [0], [1 + O(5^10)]
        [1 + O(5^10)]]
        sage: print b
        0

    An example with only double roots modulo `p`::

        sage: _.<s,t> = PolynomialRing(Qp(5,10))
        sage: f1 = s - 11* t + 5*s*t
        sage: f2 = s - t
        sage: a, b = hensel_lift_n([f1, f2], 5, 10)
        sage: print a
        []
        sage: print b
        5


    REFERENCES:

    - [S15]: \B. Schmidt, "Solutions to Systems of Multivariate p-adic Power Series".
      Oxford MSc Thesis, 2015.
    """
    precvec = []
    k = 0
    for F in flist:
        R1 = flist[k].parent()
        F1 = R1.base_ring()
        if F1.is_exact():
            precision1 = prec
        else:
            precision1 = F1.precision_cap()
            if prec > F1.precision_cap():
                print 'Cannot get %s digits of precision due to precision of inputs of f1; raise precision of inputs' %prec
            if prec < F1.precision_cap():
                precision1 = prec
        precvec.append(precision1)
        k = k+1
    precision = min(precvec);
    #print 'Precision is', precision
    slist = list(var('s%d' % i) for i in (1..len(flist)))
    s = ''
    for i in range(len(flist)):
        s += str(slist[i])+','
    a = s[0:len(s)-1]
    R = Qp(p, precision,'capped-rel')[a]
    flistnew = []
    for F in flist:
        F = R(F)
        flistnew.append(F)
    Jlist=[]
    for F in flistnew:
        for cars in list(flistnew[0].parent().gens()):
            Jlist.append(F.derivative(cars))
    J = matrix(len(flistnew), len(flistnew), Jlist)
    M = J.determinant()
    from itertools import product
    lists = []
    for i in range(len(flistnew)):
        lists.append([j for j in range(p)])
    coords = []
    for items in product(*lists):
        coords.append(items)
    roots = []
    roots_info = []
    nonroots = 0
    for i in range(len(coords)):
        valuesval = [(F(*coords[i]).valuation()) for F in flistnew]
        min_valuesval = min(valuesval)
        ord_det_J = (M(*coords[i])).valuation()
        #if min_valuesval > 2*ord_det_J: #FB: changed this
        if min(valuesval) > 0 and M(*coords[i]).valuation() == 0:
            roots.append(coords[i])
            roots_info.append([min_valuesval - 2*ord_det_J, ord_det_J])
        elif min_valuesval > 0 :
            nonroots += 1

    #print 'Roots =', roots
    actual_roots = []
    for r in roots:
        ind_roots = roots.index(r)
        rt_info = roots_info[ind_roots]
        if rt_info[0] == infinity:
            actual_roots.append(matrix(len(flist), 1, r))
        else:
            variables = []
            k = 0
            i_l = matrix(len(flist), 1, r)
            Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])

            B = (Jeval.transpose() * Jeval)
            while k < ceil(log(RR((prec-rt_info[1])/rt_info[0]))/log(2.)) + 1 and (Jeval.transpose()*Jeval).determinant() != 0: #FB:changed this
                A = matrix(len(flistnew), 1, [-f(*r) for f in flistnew]);
                i_l = i_l + ~B*Jeval.transpose()*A #NB: ~B*Jeval.transpose() == Jeval.inverse()
                for i in (0..len(flist)-1):
                    variables.append(i_l[i, 0])
                r = variables
                variables = []
                k = k+1;
                Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])
                #FB: added the following line
                B = (Jeval.transpose() * Jeval)
            actual_roots.append(i_l)

    return actual_roots, nonroots


def two_variable_padic_system_solver(G, H, p, prec1, prec2):
    r"""
    Solve systems of two `p`-adic polynomials in two variables
    by combining naive lifting of roots with the multivariable
    Hensel's lemma. See Appendix A, Algorithm 1 (4) of [BBBM19].

    INPUT:

    - ``G``, ``H`` -- polynomials over `\ZZ_p`, normalised so
      that the minimal valuation of the coefficients is `0`.

    - ``p`` -- the prime of the first input.

    - ``prec1`` -- precision for initial naive lifting.

    - ``prec2`` -- the `p`-adic precision at which we would like to
      compute the roots of `G` and `H`. `prec2` should be at most
      equal to the precision of the coefficients of `G` and `H`.

    OUTPUT:

    A tuple consisting of:

    - A list `L` of common roots in `Qp(p, prec2')^2` of `G` and `H`
      (each root is returned as a `2`-tuple, where the `i`-th entry
      corresponds to the `i`-th variable; prec2' is an integer `\le prec2`).

    - an integer `n`: the number of roots in `L` which might not lift to
      a root in `\QQ_p^2` or might not lift uniquely. In particular, if `n`
      is zero, then there is a bijection between `L` and the common roots of
      `G` and `H`.
      If `n` is positive, then the roots in `L` which force `n` to be
      positive are returned modulo `p^{prec1-3}`.


    EXAMPLES:

    An example with no double roots modulo `p` (the same example as `hensel_lift_n`)::

        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s + t - 2*s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1,f2, 5, 4, 10)
        sage: print a
        [(1 + O(5^10), 1 + O(5^10)), (0, 0)]
        sage: print b
        0


    An example with double roots modulo `p` (the same example as `hensel_lift_n`)::

        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s - 11* t + 5*s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1, f2, 5, 6, 10)
        sage: print a
        [(2 + O(5^5), 2 + O(5^5)), (0, 0)]
        sage: print b
        0


    An example of an actual double root::

        sage: _.<s, t> = PolynomialRing(Qp(5, 10))
        sage: f1 = s*t
        sage: f2 = s - t
        sage: a, b = two_variable_padic_system_solver(f1, f2, 5, 6, 10)
        sage: print a
        [(O(5^3), O(5^3))]
        sage: print b
        1

    """
    K = Qp(p, prec2)
    sols = []
    x,y = G.variables()
    Zxy.<x,y> = PolynomialRing(ZZ)
    gprec = Zxy(G)
    hprec = Zxy(H)

    #Find roots modulo p^prec1 by naive lifting
    for i in range(1, prec1 + 1):
        modulus_one_less = p^(i-1)
        tempsols = []
        temp_new_list = []
        temp_fct_list = []
        if i == 1:
            for k in range(p):
                x1 = GF(p)(k)
                for j in range(p):
                    y1 = GF(p)(j)
                    if gprec(x1, y1) % p == 0:
                        if hprec(x1, y1) % p == 0:
                            tempsols.append(vector([ZZ(x1), ZZ(y1)]))
                            temp_fct_list.append([gprec, hprec])
                            temp_new_list.append(vector([ZZ(x1), ZZ(y1)]))
            sols = tempsols
            fct_list = temp_fct_list
            new_list = temp_new_list
        else:
            for ind in range(len(sols)):
                gnew = Zxy(fct_list[ind][0](sols[ind][0] + p*x, sols[ind][1] + p*y)/p)
                hnew = Zxy(fct_list[ind][1](sols[ind][0] + p*x, sols[ind][1] + p*y)/p)
                for k in range(p):
                    x1 = GF(p)(k)
                    for j in range(p):
                        y1 = GF(p)(j)
                        one = gnew(x1, y1)
                        if one % p == 0:
                            two = hnew(x1, y1)
                            if two % p == 0:
                                xnew = new_list[ind][0] + k*modulus_one_less
                                ynew = new_list[ind][1] + j*modulus_one_less
                                tempsols.append(vector([ZZ(x1), ZZ(y1)]))
                                temp_fct_list.append([gnew, hnew])
                                temp_new_list.append([xnew, ynew])
            sols = tempsols
            fct_list = temp_fct_list
            new_list = temp_new_list

    #Reduce the roots modulo prec1-3 to avoid spurious sols
    sols = [(K(x) + O(p^(prec1-3)), K(y) + O(p^(prec1-3))) for (x,y) in new_list]
    sols = sorted(set(sols))

    #Now apply multivariable Hensel on the roots that are
    #simple modulo prec1-3
    flist = [G,H]
    precvec = []
    k = 0
    for F in flist:
        R1 = flist[k].parent()
        F1 = R1.base_ring()
        if F1.is_exact():
            precision1 = prec2
        else:
            precision1 = F1.precision_cap()
            if prec2 > F1.precision_cap():
                print 'Cannot get %s digits of precision due to precision of inputs of f1; raise precision of inputs' %prec
            if prec2 < F1.precision_cap():
                precision1 = prec2
        precvec.append(precision1)
        k = k+1
    precision = min(precvec);
    #print 'Precision is', precision
    slist = list(var('s%d' % i) for i in (1..len(flist)))
    s = ''
    for i in range(len(flist)):
        s += str(slist[i])+','
    a = s[0:len(s)-1]
    R = Qp(p,precision,'capped-rel')[a]
    flistnew=[]
    for F in flist:
        F = R(F)
        flistnew.append(F)
    Jlist=[]
    for F in flistnew:
        for cars in list(flistnew[0].parent().gens()):
            Jlist.append(F.derivative(cars))
    J = matrix(len(flistnew), len(flistnew), Jlist)
    M = J.determinant()
    from itertools import product
    roots = []
    roots_info = []
    roots2 = []
    for i in range(len(sols)):
        valuesval = [(F(*sols[i]).valuation()) for F in flistnew]
        min_valuesval = min(valuesval)
        ord_det_J = (M(*sols[i])).valuation()
        if min_valuesval > 2*ord_det_J:
            roots.append(sols[i])
            roots_info.append([min_valuesval - 2*ord_det_J,ord_det_J])
        else:
            roots2.append(sols[i])

    actual_roots = list(roots2)
    for r in roots:
        ind_roots = roots.index(r)
        rt_info = roots_info[ind_roots]
        if rt_info[0] == infinity:
            actual_roots.append((K(ZZ(r[0])),K(ZZ(r[1]))))
        else:
            ind_roots = roots.index(r)
            rt_info = roots_info[ind_roots]
            variables = []
            k = 0
            r = [ZZ(r[0]),ZZ(r[1])]
            i_l = matrix(len(flist),1,r)
            Jeval = matrix(len(flistnew),len(flistnew),[f(*r) for f in Jlist])

            B=(Jeval.transpose() * Jeval)
            while k < ceil(log(RR((prec2-rt_info[1])/rt_info[0]))/log(2.))+1 and (Jeval.transpose()*Jeval).determinant() != 0:
                A = matrix(len(flistnew),1,[-f(*r) for f in flistnew]);
                i_l = i_l + ~B*Jeval.transpose()*A
                for i in (0..len(flist)-1):
                    variables.append(i_l[i,0])
                r = variables
                variables = []
                k = k+1;
                Jeval = matrix(len(flistnew), len(flistnew), [f(*r) for f in Jlist])
                #FB: added the following line
                B = (Jeval.transpose() * Jeval)
            actual_roots.append((K(i_l[0][0]), K(i_l[1][0])))

    return actual_roots, len(roots2)
