r"""
Quadratic Chabauty for elliptic curves over `\QQ`, base-changed
to imaginary quadratic fields.

The main function is `quad_chab_ell_im_quad`.
See its docstring for details on input and output and for examples.

Parts of this code were used also for computations in [BBBM19] and [Bia19].
See also:

https://github.com/bianchifrancesca/quadratic_chabauty


REFERENCES:

- [BBBM19] \J. S. Balakrishnan, A. Besser, F. Bianchi, J. S. Mueller,
  "Explicit quadratic Chabauty over number fields". To appear in
  "Isr. J. Math.".

- [BcL+16] \J. S. Balakrishnan, M. Ciperiani, J. Lang, B. Mirza, and R. Newton,
  "Shadow lines in the arithmetic of elliptic curves".
  In" Directions in number theory, volume 3".

- [Bia19] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture". To appear in "Algebra Number Theory".


"""


def anticyc_padic_height(E, P1, d, p, prec=25, bernardi=False, multi=1):
    r"""
    Compute the anticyclotomic height of a point on an elliptic curve over `\QQ`.
    This is the code used for [BcL+16], with a few documented changes (e.g. added
    supersingular case).

    INPUT:

    - ``E`` -- an elliptic curve over `\QQ`.

    - ``d`` -- a rational number which is not a perfect square.

    - ``P1`` -- a point on `E(\QQ(\sqrt(d))`.

    - ``p`` -- a prime of good reduction which splits in `\QQ(\sqrt(d))`.

    - ``prec`` -- the `p`-adic precision.

    - ``bernardi``-- True/False (default False). If False, you must have
      `p` is `\ge 5` and ordinary. Then the Mazur-Tate sigma function is used.
      If True, the Bernardi sigma function is used.

    - ``multi`` -- parameter to check quadraticity of output.

    OUTPUT:

    A p-adic number: the anticyclotomic height of P1.
    """
    Qp = pAdicField(p,prec)
    EQp = E.change_ring(Qp)
    assert E.is_good(p)# FB 28/04 and E.is_ordinary(p)
    if bernardi == False:
        assert E.is_ordinary(p)
    K.<D> = QuadraticField(d)
    h = K.class_number()
    OK = K.maximal_order()
    assert len(factor(p*OK)) == 2
    p1, p2 = factor(p*OK)
    p1 = (p1[0]^h).gens_reduced()[0]
    p2 = (p2[0]^h).gens_reduced()[0]
    psi1, psi2 = embeddings(K,p,prec)

    #embedding is chosen so that p1 is 'pi'
    if psi1(p1).valuation() > 0:
        embedding = psi1
    else:
        embedding = psi2
    assert embedding(p1).valuation() > 0

    pi,pibar = factor(p*OK)
    pi = pi[0]
    pibar = pibar[0]
    tam = lcm(E.tamagawa_numbers())
    A1 = tam*P1
    try_orders = divisors(len(E.change_ring(GF(p)).rational_points()))
    for ord in try_orders:
        B1 = ord*A1
        B1conj = (B1[0].conjugate(), B1[1].conjugate())
        B1 = EQp(embedding(B1[0]), embedding(B1[1]))
        B1conj = EQp(embedding(B1conj[0]), embedding(B1conj[1]))
        #FB - Modification so that it does't give errors when B1[1]=0 24/11/2017
        if B1[1]!=0:
            tB1 = -B1[0]/B1[1]
            tB1conj = -B1conj[0]/B1conj[1]
            if tB1.valuation() > 0 and tB1conj.valuation() > 0 and B1[0].valuation() < 0 and B1[1].valuation() <0 and B1conj[0].valuation() < 0 and B1conj[1].valuation() < 0:
                n = ord
                break
    n = n*multi
    B1 = n*A1
    if n%2 == 1:
        fn = E.change_ring(QQ).division_polynomial(n)
    else:
        fn = E.change_ring(QQ).division_polynomial(n, two_torsion_multiplicity=1)
    xA1 = A1[0]
    xB1 = B1[0]

    if n%2 == 1:
        fn_at_A1 = fn(xA1)
    else:
        fn_at_A1 = fn((A1[0], A1[1]))

    if xA1 == 0:
        d_at_A1 = 1
    else:
        d_at_A1 = K.ideal(xA1).denominator()

    try:
        d_at_A1 = prod([a^ZZ(e/2) for (a,e) in factor(d_at_A1)]) 
        d_at_A1 = (d_at_A1^h).gens_reduced()[0]
    except AttributeError:
        d_at_A1 = prod([a^(e/2) for (a,e) in factor(d_at_A1)])

    d_of_nA1_to_h = d_at_A1^(n^2)*fn_at_A1^h
    dbydconjA1=d_of_nA1_to_h/d_of_nA1_to_h.conjugate()

    NA1 = K.ideal(dbydconjA1).numerator()
    NA1g = NA1.gens_reduced()[0]
    NA1gconj = NA1g.conjugate()
    pival= (NA1gconj/NA1g).valuation(pi)
    pibarval= (NA1gconj/NA1g).valuation(pibar)
    NA1val = (NA1gconj/NA1g)
    #A1_sum_away_from_p_via_embedding = 1/(p*h)*log(embedding(NA1val),0)
    #FB: changed normalisation
    A1_sum_away_from_p_via_embedding = -1/(h)*log(embedding(NA1val),0)
    #FB: added Bernardi sigma function option
    if bernardi == False:
        sig = E.change_ring(QQ).padic_sigma(p,prec)
    else:
        sig = bernardi_sigma_function(E.change_ring(QQ),prec=prec+5)
        sig = sig(E.change_ring(QQ).formal().log(prec+5))
    B1conj = (B1[0].conjugate(), B1[1].conjugate())
    #FB: changed normalisation
    #height_at_p_A1  = 1/(p)*log(sig(embedding(-B1[0]/B1[1]))/sig(embedding(-B1conj[0]/B1conj[1])),0)
    height_at_p_A1  = -log(sig(embedding(-B1[0]/B1[1]))/sig(embedding(-B1conj[0]/B1conj[1])),0)
    height_A1 = 1/n^2*(height_at_p_A1 + A1_sum_away_from_p_via_embedding)
    height_P1 = 1/(tam^2)*height_A1
    return height_P1


def non_archimedean_local_height(P, v, p, prec, weighted=False, is_minimal=None):
    """r
    Return the local `p`-adic height of `P` at the place `v`.
    This is a modified version of the built-in function `non_archimedean_local_height`:
    the symbolic logarithm (or real logarithm) is replaced by the `p`-adic logarithm.

    INPUT:

    - ``P`` -- a point on an elliptic curve over a number field `K`.

    - ``v`` -- a non-archimedean place of `K`` or `None`.

    - ``p`` -- an odd prime.

    - ``prec`` -- integer. The precision of the computation.

    - ``weighted`` -- boolean. If False (default), the height is
      normalised to be invariant under extension of `K`. If True,
      return this normalised height multiplied by the local degree.

    OUTPUT:

    A p-adic number: the `v`-adic component of the `p`-adic height of `P`
    if `v` is a place; the sum of the components away from `p` of the
    `p`-adic height of `P` if `v` is `None`.
    """
    if v is None:
        D = P.curve().discriminant()
        K = P.curve().base_ring()
        if K is QQ:
            factorD = D.factor()
            if P[0] == 0:
                c = 1
            else:
                c = P[0].denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True, is_minimal=(e < 12))
                       for q,e in factorD if not q.divides(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True)
                       - c.valuation(q) * log(Qp(p, prec)(q))
                       for q,e in factorD if e >= 12 and q.divides(c)))
        else:
            factorD = K.factor(D)
            if P[0] == 0:
                c = K.ideal(1)
            else:
                c = K.ideal(P[0]).denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c.norm()))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True, is_minimal=(e < 12))
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True)
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            if not weighted:
                h /= K.degree()
        return h

    if is_minimal:
        E = P.curve()
        offset = ZZ.zero()
        Pmin = P
    else:
        E = P.curve().local_minimal_model(v)
        Pmin = P.curve().isomorphism_to(E)(P)
        # Silverman's normalization is not invariant under change of model,
        # but it all cancels out in the global height.
        offset = (P.curve().discriminant()/E.discriminant()).valuation(v)

    a1, a2, a3, a4, a6 = E.a_invariants()
    b2, b4, b6, b8 = E.b_invariants()
    c4 = E.c4()
    x, y = Pmin.xy()
    D = E.discriminant()
    N = D.valuation(v)
    A = (3*x**2 + 2*a2*x + a4 - a1*y).valuation(v)
    B = (2*y+a1*x+a3).valuation(v)
    C = (3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8).valuation(v)
    if A <= 0 or B <= 0:
        r = max(0, -x.valuation(v))
    elif c4.valuation(v) == 0:
        n = min(B, N/2)
        r = -n*(N-n)/N
    elif C >= 3*B:
        r = -2*B/3
    else:
        r = -C/4
    r -= offset/6
    if not r:
        return Qp(p,prec)(0)
    else:
        if E.base_ring() is QQ:
            Nv = Integer(v)
        else:
            Nv = v.norm()
            if not weighted:
                r = r / (v.ramification_index() * v.residue_class_degree())
        return r * log(Qp(p,prec)(Nv))


def local_heights_at_bad_primes_number_field(E, L, K):
    """r
    Finds all possible sums of local heights at bad places for an integral point.

    INPUT:

    - ``E`` -- an elliptic curve, either over `\QQ`, or over the number field ``L``.

    - ``L`` -- a number field.

    - ``K`` -- a `p`-adic field, such that `E/L` has good reduction at all primes of L
      above `p`.

    OUTPUT:

    A list of `p`-adic numbers such that if `P\in E(L)` is integral (with respect to the
    given model), then the sum of the local heights away from p of the cyclotomic `p`-adic
    height of `P` belongs to this list.
    """
    E = E.change_ring(L)
    BadPrimes = E.base_ring()(E.integral_model().discriminant()).support()
    W = []
    BadPrimesNew = []
    for q in BadPrimes:
        Eq = E.local_minimal_model(q)
        deltaq = E.discriminant()/Eq.discriminant()
        qnorm = q.norm()
        if Eq.tamagawa_number(q) == 1 and deltaq.valuation(q) == 0:
            continue
        BadPrimesNew.append(q)
        ks = E.kodaira_symbol(q)
        if Eq.tamagawa_number(q) == 1 and deltaq.valuation(q) != 0:
            W.append([2*K(k)*K(qnorm).log() for k in range(1,ZZ(deltaq.valuation(q)/12)+1)])
        elif Eq.has_additive_reduction(q):
            if ks == KodairaSymbol(3): #III
                W.append([-1/2*(K(qnorm)).log()])
            elif ks == KodairaSymbol(4): #IV
                W.append([-2/3*K(qnorm).log()])
            elif ks == KodairaSymbol(-1): #I0*
                W.append([-K(qnorm).log()])
            elif ks == KodairaSymbol(-4): #IV*
                W.append([-(4/3)*K(qnorm).log()])
            elif ks == KodairaSymbol(-3): #III*
                W.append([-(3/2)*K(qnorm).log()])
            else: #Im*
                if E.tamagawa_number(q) == 2:
                    W.append([-K(qnorm).log()])
                else:
                    n = -5
                    while ks != KodairaSymbol(n):
                        n = n-1
                    m = -n-4
                    W.append([-K(qnorm).log(),-(m+4)/4*K(qnorm).log()])
        else: #multiplicative
            n = 5
            while ks != KodairaSymbol(n):
                n = n+1
            m = n-4
            if E.tamagawa_number(q) == 2:
                W.append([-m/4*K(qnorm).log()])
            else:
                W.append([-i*(m-i)/m*(K(qnorm)).log() for i in range(1,(m/2).floor()+1)]) #enough to go to m/2 -see Silverman's article

        if qnorm != 2 or E.has_split_multiplicative_reduction(q) == False:
            W[-1].append(0)

        if deltaq != 1:
            W[-1] = list(Set(W[-1] + [2*K(k)*K(qnorm).log() for k in range(1,ZZ(deltaq.valuation(q)/12)+1)]))
            W[-1] = [w - 1/6*L(deltaq).valuation(q)*K(qnorm).log() for w in W[-1]]

    W = list(itertools.product(*W))
    possible_sums = []
    for i in W:
        possible_sums.append(sum(list(i)))

    return possible_sums


def generators_over_quadratic_field(EL):
    r"""
    Find generators of (a finite index subgroup) of the free part of
    the Mordell--Weil group of the base-change over a quadratic field
    of an elliptic curve over ``\QQ``.
    This is essentially the built-in function `gens_quadratic`.

    INPUT:

    - ``EL`` -- the base-change over a quadratic field `L` of an elliptic
      curve over ``\QQ``.

    OUTPUT:

    The generators of `EL(L)` modulo torsion. When E has rank `1` over
    `\QQ` and `2` over `L`, the first point returned generates E(Q);
    the second one is in  `EL(L)^-`, up to automorphism, provided that E
    is not isomorphic over Q to the quadratic twist of E by disc(L)
    (which can only happen if `j=1728 ` and `L=Q(i) `).


    EXAMPLES:

        sage: E = EllipticCurve("143a1")
        sage: L.<a> = QuadraticField(6)
        sage: generators_over_quadratic_field(E.change_ring(L))
        [(4 : 6 : 1), (301/150 : 1001/4500*a - 1/2 : 1)]

    An example with `j`-invariant 1728:

        sage: E = EllipticCurve("256b1")
        sage: L.<a> = QuadraticField(-1)
        sage: EL = E.change_ring(L)
        sage: generators_over_quadratic_field(EL)
        [(-1 : 1 : 1), (-1/2*a : -3/4*a - 3/4 : 1)]
        sage: E.j_invariant()
        1728

    An example with extra automorphisms:

        sage: E = EllipticCurve([0,-4])
        sage: L.<a> = QuadraticField(-3)
        sage: EL = E.change_ring(K)
        sage: gens = generators_over_quadratic_field(EL)
        sage: gens
        [(2 : 2 : 1), (-a + 1 : 2*a : 1)]
        sage: auts = EL.automorphisms()
        sage: auts[1](gens[1])
        (-2 : 2*a : 1)
    """
    L = EL.base_ring()
    EE = EL.descend_to(QQ)
    if EE[0] == EL.change_ring(QQ):
        EQ1 = EE[0]
        EQ2 = EE[1]
    else:
        EQ1 = EE[1]
        EQ2 = EE[0]
    iso1 = EQ1.change_ring(L).isomorphism_to(EL)
    iso2 = EQ2.change_ring(L).isomorphism_to(EL)
    gens1 = [iso1(P) for P in EQ1.gens()]
    gens2 = [iso2(P) for P in EQ2.gens()]
    return gens1 + gens2


def sorting_fct(L):
    r"""
    Return `0` if input has length `2`, `1` otherwise.
    """
    if len(L) == 2:
        return 0
    else:
        return 1


############## MAIN FUNCTION ###############


def quad_chab_ell_im_quad(E, p, n, double_root_prec, L, int_list = [], bernardi = False, up_to_auto = False):
    r"""
    Do quadratic Chabauty for an elliptic curve `E` over
    `\QQ`, base-changed to an imaginary quadratic field `L`.
    `E` should have rank `1` over `\QQ` and rank `2` over `L`

    INPUT:

    - ``E`` -- an elliptic curve of rank `1` over `\QQ`.

    - ``L`` -- an imaginary quadratic field, such that `E(L)` has rank 2
      and such that all the primes of bad reduction for `E` with non-trivial
      Tamagawa number are ramified or inert in `L`.

    - ``p`` -- a prime of good reduction for `E`, split in `L`.

    - ``n`` -- `p`-adic precision.

    - ``double_root_prec`` -- auxiliary precision used in the solution of
      `2`-variable systems of `2`-equations when these have double roots
      modulo `p`. Cf. the variable `prec1` in `two_variable_padic_system_solver`.

    - ``int_list``(optional) -- a list of known integral points of `E/L`.
      If `double_root_prec` is not large enough to resolve a double root
      in a residue pair containing some point in `int_list`, the resolution
      is attempted with `double_root_prec + 2`. If this does not suffice and
      the given residue pair contains the points `P_1,..,P_m` in
      `int_list`, then the statement "A double root in a disc with the known
      integral points [P_1,..., P_m]" is printed.

    - ``bernardi``-- True/False (default False): if False and `p` is `\ge 5` and ordinary,
      the Mazur-Tate sigma function is used; otherwise, the Bernardi one.

    - ``up_to_auto`` -- True/False (default False): If True, the points in the
      output will be up to hyperelliptic involution and reversing.

    OUTPUT: A tuple consisting of

    (1) A list of points in `E(\ZZ)`: the points in the `p`-adic quadratic Chabauty
      output which were recognised as points in `E(\ZZ)`. If one of such points in
      `int_list` is not recovered in the computation, the statement "The following
      integral point was not detected:..." is printed.

    (2) A list of points in `E(O_L)`: the points in the `p`-adic quadratic Chabauty
      output which were recognised as points in `E(O_L) \setminus E(\ZZ)`.If one of
      such points in `int_list` is not recovered in the computation, the statement
      "The following integral point was not detected:..." is printed.

    (3) A list of lists. The first two entries of the lists represent points in
      `E(\QQ_p)\times E(\QQ_p)` (modulo a `p`-adic precision dependent on `n` and
      `double_root_prec`):
      the points in the `p`-adic quadratic Chabauty output that were not recognised
      as points in `E(\ZZ)` but which are of the form `(P, P)` for some `P` in `E(\QQ_p)`.
      The third entry of a list gives information on the value of the cyclotomic local
      heights away from `p` for which the given point was recovered. This information is given
      as an integer: the index in the set `W` of possible sums of heights away from `p`
      (The set `W` is printed in the computation.)

    (4) A list of lists. points in `E(\QQ_p)\times E(\QQ_p)` (modulo a `p`-adic precision
      dependent on `n` and `double_root_prec`): all the points in the `p`-adic
      quadratic Chabauty output that are not in the previous three lists.
      As in the previous output item, the index of the corresponding cyclotomic height value
      at bad primes is returned. Note: if a point is recognised as algebraic, it is
      represented as a tuple of minimal polynomials/rational numbers, rather than
      as a point in `E(\QQ_p)\times E(\QQ_p)`.

    (5) An integer: the number of residue pairs for which the computation could not
      establish if the recovered points lift to solutions over `\QQ_p` or if they
      lift uniquely. Note that if this occurs in a disk containing a point in
      `int_list`, the statement "A double root in a disc with the known integral points..."
      is printed during the computation.

   .. NOTE::

      If the `p`-adic precision is too low, some integral points may not be recognised
      as such and will appear in (3) or (4).

    EXAMPLES:

        sage: E = EllipticCurve("91a1")
        sage: K.<a> = QuadraticField(-1)
        sage: int_points = [(-a - 1, a - 2, 1), (-a - 1, -a + 1, 1), (a - 1, -a - 2, 1), (a - 1, a + 1, 1), (-a, -1, 1), (-a, 0, 1), (0,-1, 1), (0, 0, 1), 
        ....: (a, - 1, 1), (a, 0, 1), (1, -2, 1), (1, 1, 1), (-42*a + 2, -206*a - 179, 1), (-42*a + 2, 206*a + 178, 1), (42*a + 2, 206*a - 179, 1), (42*a +
        ....:  2, -206*a + 178, 1), (3, -6, 1), (3, 5, 1), (-2*a + 4, 6*a - 8, 1), (-2*a + 4, -6*a + 7, 1), (2*a + 4, -6*a - 8, 1), (2*a + 4, 6*a + 7, 1)]
        sage: A = quad_chab_ell_im_quad(E, 5, 20, 5, K, int_list = int_points)
        W is [0]
        sage: print "Q-integral points recovered:", A[0]
        Q-integral points recovered: [(0 : 0 : 1), (0 : -1 : 1), (3 : 5 : 1), (3 : -6 : 1), (1 : -2 : 1), (1 : 1 : 1)]
        sage: print "Other integral points recovered: ", A[1]
        Other integral points recovered: [(2*a + 4 : 6*a + 7 : 1), (2*a + 4 : -6*a - 8 : 1), (-2*a + 4 : 6*a - 8 : 1), (a : 0 : 1), (42*a + 2 : -206*a + 178
        : 1), (-2*a + 4 : -6*a + 7 : 1), (a : -1 : 1), (42*a + 2 : 206*a - 179 : 1), (-a : 0 : 1), (a - 1 : -a - 2 : 1), (-a : -1 : 1), (a - 1 : a + 1 : 1),
        (-42*a + 2 : -206*a - 179 : 1), (-a - 1 : -a + 1 : 1), (-42*a + 2 : 206*a + 178 : 1), (-a - 1 : a - 2 : 1)]
        sage: print "Number of extra points:", len(A[2]) + len(A[3])
        Number of extra points: 98
        sage: print "Number of discs for which double roots were unresolved:", A[4]
        Number of discs for which double roots were unresolved: 0


    If, in the same example, we do not provide a list of known integral points, we need to increase `double_root_prec`;
    furthermore, if we do not increase `n`, the integral points (-42*a + 2 : -206*a - 179 : 1), (-42*a + 2 : 206*a + 178 : 1)
    (42*a + 2 : 206*a - 179 : 1), (42*a + 2 : -206*a + 178 : 1) will not appear in A[1], but their images under the completion
    maps will be in A[3]::

        sage: A = quad_chab_ell_im_quad(E, 5, 20, 7, K)
        W is [0]
        sage: print len(int_points) - (len(A[0]) + len(A[1]))
        4
        sage: print A[0]
        [(0 : 0 : 1), (0 : -1 : 1), (3 : 5 : 1), (3 : -6 : 1), (1 : -2 : 1), (1 : 1 : 1)]
        sage: print A[1]
        [(2*a + 4 : 6*a + 7 : 1), (2*a + 4 : -6*a - 8 : 1), (-2*a + 4 : 6*a - 8 : 1), (a : 0 : 1), (-2*a + 4 : -6*a + 7 : 1), (a : -1 : 1), (-a : 0 : 1), (a
        - 1 : -a - 2 : 1), (-a : -1 : 1), (a - 1 : a + 1 : 1), (-a - 1 : -a + 1 : 1), (-a - 1 : a - 2 : 1)]
        sage: f1 = (-42*a+2).minpoly()
        sage: f2 = (-206*a - 179).minpoly()
        sage: for P in A[3]:
        ....:     if f1(P[0][0]) == 0 and f2(P[0][1]) == 0 and f1(P[1][0]) == 0 and f2(P[1][1]) == 0:
        ....:         print P
        ....:         print "---------"
        [(3 + 5 + 4*5^2 + 3*5^3 + 5^4 + 4*5^5 + 5^6 + 4*5^7 + 4*5^8 + 2*5^9 + 4*5^10 + 3*5^11 + 3*5^12 + 2*5^13 + O(5^14) : 4 + 3*5^2 + 3*5^3 + 5^4 + 5^6 +
        5^7 + 2*5^8 + 2*5^9 + 3*5^10 + 4*5^11 + O(5^14) : 1 + O(5^20)), (1 + 4*5 + 5^3 + 3*5^4 + 3*5^6 + 2*5^9 + 5^11 + 5^12 + 2*5^13 + O(5^14) : 3 + 2*5 +
        2*5^2 + 3*5^3 + 2*5^4 + 4*5^5 + 3*5^6 + 3*5^7 + 2*5^8 + 2*5^9 + 5^10 + 4*5^12 + 4*5^13 + O(5^14) : 1 + O(5^20)), 0]
        ---------
        [(1 + 4*5 + 5^3 + 3*5^4 + 3*5^6 + 2*5^9 + 5^11 + 5^12 + 2*5^13 + O(5^14) : 3 + 2*5 + 2*5^2 + 3*5^3 + 2*5^4 + 4*5^5 + 3*5^6 + 3*5^7 + 2*5^8 + 2*5^9 +
        5^10 + 4*5^12 + 4*5^13 + O(5^14) : 1 + O(5^20)), (3 + 5 + 4*5^2 + 3*5^3 + 5^4 + 4*5^5 + 5^6 + 4*5^7 + 4*5^8 + 2*5^9 + 4*5^10 + 3*5^11 + 3*5^12 +
        2*5^13 + O(5^14) : 4 + 3*5^2 + 3*5^3 + 5^4 + 5^6 + 5^7 + 2*5^8 + 2*5^9 + 3*5^10 + 4*5^11 + O(5^14) : 1 + O(5^20)), 0]
        ---------

    """

    #Trivial cases: TO DO (cf. Theorem 1.6, 1.7 (1) of [Bia19])
    #Non-trivial cases:

    if up_to_auto == True:
        print "Note that you have chosen to consider residue disks up to automorphisms and reversing"
        sys.stdout.flush()

    rankQ = E.rank()
    K = pAdicField(p, n)
    Zpn = Zp(p, prec = n, type = 'fixed-mod', print_mode = 'series')
    _.<x> = PolynomialRing(E.base_ring())
    Eshort = E.short_weierstrass_model()
    phi = Eshort.isomorphism_to(E)
    psi = E.isomorphism_to(Eshort)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    [u, rr, s, tt] = psi.tuple()
    OL = L.maximal_order()
    p1, p2 = factor(p*OL)
    p1 = (p1[0]^L.class_number()).gens_reduced()[0]
    p2 = (p2[0]^L.class_number()).gens_reduced()[0]
    EMBD1, EMBD2 = embeddings(L, p, n+5)

    #embedding is chosen so that p1 is 'pi'
    if EMBD1(p1).valuation() > 0:
        embd1 = EMBD1
        embd2 = EMBD2
    else:
        embd1 = EMBD2
        embd2 = EMBD1
    assert embd1(p1).valuation() > 0


    #Assume for simplicity that all the bad primes are ramified or inert in L
    #so that the local anticyclotomic heights away from p are all trivial.
    for q in E.conductor().factor():
        if len((q[0]*OL).factor()) != 1:
            if E.is_minimal() == False or E.tamagawa_number(q[0])!= 1:
                print "Currently implemented only for quadratic fields in which the bad primes are ramified or inert"
                sys.stdout.flush()
    H = HyperellipticCurve(x^3 + a4*x + a6)
    if E.is_ordinary(p) and bernardi == False:
        sigma = E.padic_sigma(p,n)
        val_sigma = 0
    else:
        bernardi = True
        sigma = bernardi_sigma_function(E, prec=n)
        sigma = sigma(E.formal().log(n))
        val_sigma = max(sigma[i].denominator().valuation(p) for i in range(sigma.precision_absolute()))

    EL = E.change_ring(L)
    [P1min, P2min] = generators_over_quadratic_field(EL)
    assert P1min in E and P2min not in E

    HK = H.change_ring(K)
    EK = E.change_ring(K)
    HZpn = H.change_ring(Zpn)
    Hp = H.change_ring(GF(p))
    Epshort = Eshort.change_ring(GF(p))
    SK = K[['t']]
    t = SK.gen()
    SK.set_default_prec(n+2)

    #cyclotomic height of P1 (anticyc is 0)
    if bernardi == False:
        h = E.padic_height(p, n)
        hP1 = h(E(P1min))
    else:
        hP1 = height_bernardi(E(P1min), p, n)

    #cyclotomic and anticyclotomic height of P2 and P1 + P2
    #note the anticyclotomic height of P2 is zero
    mP = E.Np(p)
    fmP = E.division_polynomial(mP, two_torsion_multiplicity=1)
    mPP2 = mP*P2min
    P3min = P2min+P1min
    mPP12 = mP*P3min
    fmPP2 = fmP(P2min[0], P2min[1])
    fmPP12 = fmP(P3min[0], P3min[1])
    sigmamPP2_1 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd1(mPP2[0]/mPP2[1]))))
    sigmamPP2_2 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd2(mPP2[0]/mPP2[1]))))
    sigmamPP12_1 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd1(mPP12[0]/mPP12[1]))))
    sigmamPP12_2 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd2(mPP12[0]/mPP12[1]))))
    fmPP2_1 = pAdicField(p,n-val_sigma-2)(embd1(fmPP2))
    fmPP2_2 = pAdicField(p,n-val_sigma-2)(embd2(fmPP2))
    fmPP12_1 = pAdicField(p,n-val_sigma-2)(embd1(fmPP12))
    fmPP12_2 = pAdicField(p,n-val_sigma-2)(embd2(fmPP12))
    try:
        hP2 =  -(log(sigmamPP2_1/fmPP2_1) + log(sigmamPP2_2/fmPP2_2))/mP^2 + non_archimedean_local_height(P2min, None, p, n)
        hP12 =  -(log(sigmamPP12_1/fmPP12_1) + log(sigmamPP12_2/fmPP12_2))/mP^2 +  non_archimedean_local_height(P3min, None, p, n)
    except ValueError:
        print "Sorry, We are currently assuming that the generators of E(L) and their sum are integral at p; minor modifications needed to remove the assumption"
        return "Unknown"
    hP12_anti = anticyc_padic_height(E, P3min, L.discriminant(), p, prec=n, multi=1, bernardi=bernardi)

    #Compute Frobenius data only once:
    M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    forms = [form.change_ring(K) for form in forms]
    M_sys = matrix(K, M_frob).transpose() - 1
    inverse_frob = M_sys**(-1)

    #Compute constants alpha_cyc and alpha_anti:
    P1 = psi(P1min)
    P2 = psi(P2min)
    A = coleman_integrals_on_basis(HK, HK(0,1,0), HK(P1[0],P1[1]), inverse_frob, forms)[0]
    B1 = coleman_integrals_on_basis(HK,HK(0,1,0), HK(embd1(P2[0]),embd1(P2[1])), inverse_frob, forms)[0]
    B2 = coleman_integrals_on_basis(HK,HK(0,1,0), HK(embd2(P2[0]),embd2(P2[1])), inverse_frob, forms)[0]
    a11 = 1/4*B2^2/(1/4*A^2*B1^2 - 1/2*A^2*B1*B2 + 1/4*A^2*B2^2)
    a12 = (-1/2*B2)/(1/4*A*B1^2 - 1/2*A*B1*B2 + 1/4*A*B2^2)
    a13 = 1/(B1^2 - 2*B1*B2 + B2^2)
    a21 = (-1/2*B1*B2)/(1/4*A^2*B1^2 - 1/2*A^2*B1*B2 + 1/4*A^2*B2^2)
    a22 = (1/2*B1 + 1/2*B2)/(1/4*A*B1^2 - 1/2*A*B1*B2 + 1/4*A*B2^2)
    a23 = (-2)/(B1^2 - 2*B1*B2 + B2^2)
    a31 = 1/2*B1^2/(1/2*A^2*B1^2 - A^2*B1*B2 + 1/2*A^2*B2^2)
    a32 = (-B1)/(1/2*A*B1^2 - A*B1*B2 + 1/2*A*B2^2)
    a33 = 1/(B1^2 - 2*B1*B2 + B2^2)
    M_inv = Matrix(K, [[a11, a12, a13],[a21, a22, a23], [a31, a32, a33]])
    vec_cyc = vector([hP1, 1/2*(hP12-hP1-hP2), hP2])
    vec_anti = vector([K(0), 1/2*(hP12_anti), K(0)])
    alphas_cyc =  M_inv*vec_cyc
    alphas_anti = M_inv*vec_anti

    #the residue pairs we need to consider:
    PointsModp = list(Hp.points())
    classes_to_consider_0 = [Q for Q in itertools.product(PointsModp, PointsModp)]
    if up_to_auto == False:
        classes_to_consider = classes_to_consider_0
    else:
        classes_to_consider = []
        for Q in classes_to_consider_0:
            Qaut = (Hp(Q[0][0], -Q[0][1], Q[0][2]), Hp(Q[1][0], -Q[1][1], Q[1][2]))
            Qrev = (Q[1], Q[0])
            if Qaut in classes_to_consider or Qrev in classes_to_consider:
                continue
            classes_to_consider.append(Q)

    OrderPointsPairs = []
    OrderPoints2 = []
    for Q in classes_to_consider:
        Q1 = Q[0]
        Q2 = Q[1]
        mQ1 = Eshort.change_ring(GF(p))(Q1).order()
        mQ2 = Eshort.change_ring(GF(p))(Q2).order()
        OrderPointsPairs.append([mQ1,mQ2])
        OrderPoints2.append(mQ1)
        OrderPoints2.append(mQ2)
    OrderPoints = list(Set(OrderPoints2))

    OrderDivPoly = [[0, 0] for i in range(len(OrderPointsPairs))]
    for mQ in OrderPoints:
        if mQ%2 != 0:
            fmQ = E.division_polynomial(mQ)
        else:
            fmQ = E.division_polynomial(mQ, two_torsion_multiplicity=1)
        for i in range(len(OrderPointsPairs)):
            if OrderPointsPairs[i][0] == mQ:
                OrderDivPoly[i][0] = fmQ
            if OrderPointsPairs[i][1] == mQ:
                OrderDivPoly[i][1] = fmQ

    number_Fp_points = len(Hp.points())

    W = local_heights_at_bad_primes_number_field(E, L, K)
    print "W is", W
    sys.stdout.flush()

    int_list_new = []
    int_list_new_embedded = []
    base_points = []
    for int_pt in int_list:
        int_pt = EL(int_pt[0], int_pt[1])
        bad_height_int_pt = non_archimedean_local_height(int_pt, None, p, n)
        ind_W = W.index(2*bad_height_int_pt)
        sys.stdout.flush()
        int_pt_1 = EK(embd1(int_pt[0]), embd1(int_pt[1]))
        int_pt_2 = EK(embd2(int_pt[0]), embd2(int_pt[1]))
        int_pt_1_short = psi(int_pt_1)
        int_pt_2_short = psi(int_pt_2)
        int_mod_p = (Hp(int_pt_1_short[0]%p, int_pt_1_short[1]%p), Hp(int_pt_2_short[0]%p, int_pt_2_short[1]%p))
        if int_mod_p in base_points:
            int_list_new[base_points.index(int_mod_p)].append(int_pt)
            int_list_new_embedded[base_points.index(int_mod_p)].append([int_pt_1, int_pt_2, ind_W])
        else:
            int_list_new.append([int_pt])
            int_list_new_embedded.append([[int_pt_1, int_pt_2, ind_W]])
            base_points.append(int_mod_p)


    points = []
    integral_points_Q = []
    integral_points_L = []
    extra_points_Q = []
    extra_points_non_Q = []
    points_new = []
    integral_points_Q = []
    integral_points_L = []
    extra_points_Q = []
    extra_points_non_Q = []
    points_new = []
    double_root_count = 0
    actual_double_root_count = 0

    for Q in classes_to_consider:
        Q1 = Q[0]
        Q2 = Q[1]
        if Q1[2] == 0 or Q2[2] == 0:
                continue
        par_rat = 0
        new_points_disc = []
        if Q in base_points:
            par_rat = 1
            ind_bp = base_points.index(Q)
        indexQ = classes_to_consider.index(Q)
        m1 = OrderPointsPairs[indexQ][0]
        m2 = OrderPointsPairs[indexQ][1]
        fm1 = OrderDivPoly[indexQ][0]
        fm2 = OrderDivPoly[indexQ][1]
        R1 = Q_lift(HK, Q1, p)
        R2 = Q_lift(HK, Q2, p)
        R1Zpn = HZpn(R1)
        R2Zpn = HZpn(R2)
        xR1, yR1 =  HZpn.local_coord(R1Zpn, prec=n+2)
        xR1 = SK(xR1)
        yR1 = SK(yR1)
        dx1 = xR1.derivative()
        const_term1 = coleman_integrals_on_basis(HK, HK(0,1,0), R1, inverse_frob, forms)[0]
        log_nearR1 = (dx1/(2*yR1)).integral() + const_term1
        log_nearR1 = log_nearR1(p*t)
        xR1new = xR1(p*t)
        yR1new = yR1(p*t)
        Elocshort = Eshort.change_ring(FractionField(xR1.parent()))
        Eloc = E.change_ring(FractionField(xR1.parent()))
        xR1E = u^2*xR1new + rr
        yR1E = u^3*yR1new + s*u^2*xR1new + tt

        xR2, yR2 =  HZpn.local_coord(R2Zpn, prec=n+2)
        xR2 = SK(xR2)
        yR2 = SK(yR2)
        dx2 = xR2.derivative()
        const_term2 = coleman_integrals_on_basis(HK, HK(0,1,0), R2, inverse_frob, forms)[0]
        log_nearR2 = (dx2/(2*yR2)).integral() + const_term2
        log_nearR2 = log_nearR2(p*t)
        xR2new = xR2(p*t)
        yR2new = yR2(p*t)
        Elocshort = Eshort.change_ring(FractionField(xR2.parent()))
        Eloc = E.change_ring(FractionField(xR2.parent()))
        xR2E = u^2*xR2new + rr
        yR2E = u^3*yR2new + s*u^2*xR2new + tt

        PointaroundR1 = Eloc(xR1E, yR1E)
        PointaroundR2 = Eloc(xR2E, yR2E)
        mxR1yR1 = m1*PointaroundR1
        mxR2yR2 = m2*PointaroundR2
        sigma_nearmR1 = sigma.truncate(n)((-mxR1yR1[0]/mxR1yR1[1]).power_series())
        sigma_nearmR2 = sigma.truncate(n)((-mxR2yR2[0]/mxR2yR2[1]).power_series())

        if m1%2 != 0:
            fm1_nearR = fm1(xR1E)
        else:
            fm1_nearR = fm1(xR1E,yR1E)
        if m2%2 != 0:
            fm2_nearR = fm2(xR2E)
        else:
            fm2_nearR = fm2(xR2E,yR2E)
        sigmaoverfm_near1 = sigma_nearmR1/fm1_nearR
        sigmaoverfm_near2 = sigma_nearmR2/fm2_nearR
        h_nearR_1 = -2*((sigmaoverfm_near1/sigmaoverfm_near1[0]).log(prec=n) + sigmaoverfm_near1[0].log())/m1^2 #Note that if the reduction is supersingular the coefficients of the series will be correct only up to the given absolute precision - val_sigma. This is taken care of in the roots but not here, that is some digits of h could be wrong
        h_nearR_2 = -2*((sigmaoverfm_near2/sigmaoverfm_near2[0]).log(prec=n) + sigmaoverfm_near2[0].log())/m2^2

        two_variable.<t1,t2> = PowerSeriesRing(h_nearR_1[0].parent())
        h0 = (1/2)*(h_nearR_1(t1) + h_nearR_2(t2))
        f0 =  h0 - alphas_cyc[0]*log_nearR1(t1)^2 - alphas_cyc[1]*log_nearR1(t1)*log_nearR2(t2) - alphas_cyc[2]*log_nearR2(t2)^2
        fW = [f0 + w/2 for w in W]
        h_anti = (1/2)*(h_nearR_1(t1) - h_nearR_2(t2))
        f_anti = h_anti - alphas_anti[0]*log_nearR1(t1)^2  - alphas_anti[2]*log_nearR2(t2)^2

        min_deg = min(h_nearR_1.truncate().degree(), h_nearR_2.truncate().degree())

        for f in fW:
            PolRing.<T1,T2> = PolynomialRing(f[0][0].constant_coefficient().parent())
            coeffsh1 = f.coefficients()
            coeffsh2 = f_anti.coefficients()
            polh1 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v for (k,v) in coeffsh1.items()))
            polh2 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v for (k,v) in coeffsh2.items()))
            vpolh1 = min([i[0].valuation() for i in list(polh1)])
            vpolh2 = min([i[0].valuation() for i in list(polh2)])
            commonroots, doubleroots = hensel_lift_n([p^(-vpolh1)*polh1, p^(-vpolh2)*polh2], p, min(n-7, min_deg - 3))
            if doubleroots > 0:
                double_root_count += 1
                commonroots, test = two_variable_padic_system_solver(p^(-vpolh1)*polh1, p^(-vpolh2)*polh2, p, double_root_prec, min(n-7, min_deg - 3))
                if par_rat == 1 and test>0:
                    commonroots,test = two_variable_padic_system_solver(p^(-vpolh1)*polh1, p^(-vpolh2)*polh2, p, double_root_prec+2, min(n-7, min_deg - 3))
                roots = [[p*r[0],p*r[1]] for r in commonroots if r[0].valuation(p) >= 0 and r[1].valuation(p) >= 0]
                if test > 0:
                    print "test>0 for", Q
                    sys.stdout.flush()
                    actual_double_root_count += 1
                    if par_rat == 1:
                        print "A double root in a disc with the known integral points", int_list_new[ind_bp]
                        sys.stdout.flush()
            else:
                roots = [[p*r[0,0], p*r[1,0]] for r in commonroots if r[0,0].valuation(p)>= 0 and r[1,0].valuation(p)>=0]
            new_points = [[HK(xR1(K(sage_eval('%s'%t0[0]))),yR1(K(sage_eval('%s'%t0[0])))), HK(xR2(K(sage_eval('%s'%t0[1]))),yR2(K(sage_eval('%s'%t0[1])))), fW.index(f)] for t0 in roots]
            new_points = [[EK(u^2*QP[0][0] + rr, u^3*QP[0][1] + s*u^2*QP[0][0] + tt), EK(u^2*QP[1][0] + rr, u^3*QP[1][1] + s*u^2*QP[1][0] + tt), fW.index(f)] for QP in new_points]
            new_points_disc.extend(new_points)

        if par_rat == 1:
            for QP in int_list_new_embedded[ind_bp]:
                ind_QP = int_list_new_embedded[ind_bp].index(QP)
                if QP not in new_points_disc:
                    print "The following integral point was not detected:", int_list_new[ind_bp][ind_QP]
                    sys.stdout.flush()
                    continue
                QP_rat = int_list_new[ind_bp][ind_QP]
                if QP_rat[0] in QQ and QP_rat[1] in QQ:
                    integral_points_Q.append(QP_rat)
                else:
                    integral_points_L.append(QP_rat)
                new_points_disc.remove(QP)
        points.extend(new_points_disc)


    #Sorting out points:

    for A in points:
        if QQ(A[0][0]) == QQ(A[1][0]) and QQ(A[0][1]) == QQ(A[1][1]):
            try:
                NRP = E.lift_x(QQ(A[0][0]))
                if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                    integral_points_Q.append(NRP)
                else:
                    NRP = -E(NRP[0],NRP[1])
                    if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                        integral_points_Q.append(NRP)
                    else:
                        extra_points_Q.append(A)
            except ValueError:
                try:
                    NRP = E.lift_x(-QQ(-A[0][0]))
                    if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                        integral_points_Q.append(NRP)
                    else:
                        NRP = -E(NRP[0],NRP[1])
                        if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                            integral_points_Q.append(NRP)
                        else:
                            extra_points_Q.append(A)
                except ValueError:
                    extra_points_Q.append(A)
        else:
            points_new.append(A)

    if points_new != []:
        for A in points_new:
            p2 = algdep(A[0][1], 2)
            p1 = algdep(A[0][0], 2)
            p22 = algdep(A[1][1], 2)
            p12 = algdep(A[1][0], 2)
            if p22 == p2 and p1 == p12:
                Lf.<par> = NumberField(p2)
                if Lf.discriminant() == L.discriminant():
                    Lf = L
                if p1.degree() == 1:
                    try:
                        NPnotQ = E.change_ring(Lf).lift_x(QQ(A[0][0])) #For consistency with embeddings, enough to check that the y-coordinates are different
                        if p2(NPnotQ[1]) == 0 or p2((-NPnotQ)[1]) == 0:
                            if A[0][1] != A[1][1]:
                                if Lf.discriminant() == L.discriminant():
                                    if p2(NPnotQ[1]) == 0 and NPnotQ not in integral_points_L: #last condition to avoid cases where E:y^2=f(x) so if x_0\in Q then y_0^2\in Q so minpoly of y_0 same as of -y_0
                                        integral_points_L.append(NPnotQ)
                                    else:
                                        integral_points_L.append(-NPnotQ)
                                else:
                                    extra_points_non_Q.append([(QQ(A[0][0]), p2),  A[2]])
                            else:
                                extra_points_non_Q.append(A)
                        else:
                            extra_points_non_Q.append(A)
                    except ValueError:
                        extra_points_non_Q.append(A)
                else:
                    if A[0][0] == A[1][0]: #the x-coordinates better be different or they're the image under the same embedding
                        extra_points_non_Q.append(A)
                        continue
                    Lf.<par> = NumberField(p1)
                    if Lf.discriminant() == L.discriminant():
                        Lf = L
                        par = PolynomialRing(L,"x")(p1).roots()[0][0]
                    try:
                        ELf = E.change_ring(Lf)
                        NPnotQ = ELf.lift_x(par)
                        if p2(NPnotQ[1]) == 0 or p2((-NPnotQ)[1]) == 0:
                            if p2.degree() == 1:
                                if Lf.discriminant() == L.discriminant():
                                    if (embd1(par) - A[0][0]).valuation() < min(n, A[0][0].precision_absolute()) :
                                        par = PolynomialRing(L,"x")(p1).roots()[1][0]
                                    if p2(NPnotQ[1])== 0:
                                        integral_points_L.append(ELf(par, NPnotQ[1]))
                                    else:
                                        integral_points_L.append(ELf(par, (-NPnotQ)[1]))
                                else:
                                    extra_points_non_Q.append([(p1, QQ(A[0][1])), A[2]])
                            else:
                                embdsf = embeddings(Lf, p, n)
                                embd1f = embdsf[0]
                                embd2f = embdsf[1]
                                if (embd1f(par) - A[0][0]).valuation(p) >= min(n, A[0][0].precision_absolute()):
                                    embd = embd1f
                                    if (embd1f(NPnotQ[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd2f(NPnotQ[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue

                                    elif (embd1f((-NPnotQ)[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd2f((-NPnotQ)[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    else:
                                        extra_points_non_Q.append(A)
                                        continue
                                elif (embd2f(par) - A[0][0]).valuation(p) >= min(n, A[0][0].precision_absolute()):
                                    embd = embd2f
                                    if (embd2f(NPnotQ[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd1f(NPnotQ[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    elif (embd2f((-NPnotQ)[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd1f((-NPnotQ)[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    else:
                                        extra_points_non_Q.append(A)
                                        continue
                                else:
                                    extra_points_non_Q.append(A)
                                    continue
                                if Lf.discriminant() == L.discriminant():
                                    if embd(par) == embd2(par):
                                        par = PolynomialRing(L, "x")(p1).roots()[1][0]
                                        NPnotQ = ELf.lift_x(par)
                                    if embd1(NPnotQ[1]) == A[0][1]:
                                        integral_points_L.append(NPnotQ)
                                    else:
                                        integral_points_L.append(-NPnotQ)
                                else:
                                    extra_points_non_Q.append([(p1, p2), A[2]])
                        else:
                            extra_points_non_Q.append(A)
                    except ValueError:
                        extra_points_non_Q.append(A)
            else:
                extra_points_non_Q.append(A)

    extra_points_non_Q.sort(key=sorting_fct)

    return integral_points_Q, integral_points_L, extra_points_Q, extra_points_non_Q, actual_double_root_count
