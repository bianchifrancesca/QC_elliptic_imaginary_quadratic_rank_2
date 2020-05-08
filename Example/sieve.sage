E = EllipticCurve([0,-4])
K.<a> = QuadraticField(-3)
OK = K.maximal_order()
EK = E.change_ring(K)
Q = EK(2, 2)
R = EK(-a + 1, 2*a)

#int_points = [(-61*a + 61 , -778*a ),(61*a + 61 , 778*a ),(5 , 11 ),(3*a - 5 , 4*a + 18 ),(-3*a - 5 , -4*a + 18 ),(1/2*(-5*a - 5) , -11 ),(4*a - 2 , 4*a - 18 ), (1/2*(a - 1) , -a ),(2 , -2 ),(1/2*(-a - 1) , a ),(-4*a - 2 , -4*a - 18 ),(1/2*(5*a - 5) , -11 ),(a + 7 , -4*a - 18 ),(-a - 1 , 2 ),(-a + 1 , -2*a ),(a + 1 , 2*a ),(a - 1 , 2 ),(-a + 7 , 4*a - 18 ),(-122 , 778*a ),(1 , a ),(-2 , 2*a ),(-2 , -2*a ),(1 , -a ),(-122 , -778*a ),(-a + 7 , -4*a + 18 ),(a - 1 , -2 ),(a + 1 , -2*a ),(-a + 1 , 2*a ),(-a - 1 , -2 ),(a + 7 , 4*a + 18 ),(1/2*(5*a - 5) , 11 ),(-4*a - 2 , 4*a + 18 ),(1/2*(-a - 1) , -a ),(2 , 2 ),(1/2*(a - 1) , a ),(4*a - 2 , -4*a + 18),(1/2*(-5*a - 5) , 11 ),(-3*a - 5 , 4*a - 18 ),(3*a - 5 , -4*a - 18 ),(5 , -11 ),(61*a + 61 , -778*a ),(-61*a + 61 , 778*a )]
#extra_points_7 is the list A[2] + A[3]
#where A = quad_chab_ell_im_quad(E, 7, 20, 5, K, int_list = int_points, bernardi = False)
#extra_points_13 is the list A[2] + A[3]
#where A = quad_chab_ell_im_quad(E, 13, 20, 5, K, int_list = int_points, bernardi = False, up_to_auto = True)

############## INFORMATION AT p = 7 ##############

p = 7
n = 20
p1, p2 = factor(p*OK)
p1 = (p1[0]^K.class_number()).gens_reduced()[0]
p2 = (p2[0]^K.class_number()).gens_reduced()[0]
EMBD1, EMBD2 = embeddings(K, p, n+5)

#These are the embeddings used in quad_chab_ell_im_quad
if EMBD1(p1).valuation() > 0:
    psi1 = EMBD1
    psi2 = EMBD2
else:
    psi1 = EMBD2
    psi2 = EMBD1
assert psi1(p1).valuation() > 0

Ep = E.change_ring(GF(p))
Q1 = Ep(psi1(Q[0])%p, psi1(Q[1])%p)
Q2 = Ep(psi2(Q[0])%p, psi2(Q[1])%p)
R1 = Ep(psi1(R[0])%p, psi1(R[1])%p)
R2 = Ep(psi2(R[0])%p, psi2(R[1])%p)
ord_1 = lcm(Q1.order(), Q2.order())
print "The order of Q in E(F_7) x E(F_7) is", ord_1
sys.stdout.flush()
ord_2 = lcm(R1.order(), R2.order())
print "The order of R in E(F_7) x E(F_7) is", ord_2
sys.stdout.flush()

coeffs_mod_N7 = [[] for i in range(len(extra_points_7))]
for i in range(len(extra_points_7)):
    P = extra_points_7[i]
    P1 = Ep(P[0][0], P[0][1])
    P2 = Ep(P[1][0], P[1][1])
    for n in range(ord_1):
        for m in range(ord_2):
            if n*Q1 + m*R1 == P1 and n*Q2 + m*R2 == P2:
                coeffs_mod_N7[i].append([n,m]) #n is modulo ord_1, m is modulo ord_2

new_list_points_7 = []
new_list_coeffs_mod_N7 = []

for i in range(len(extra_points_7)):
    if coeffs_mod_N7[i] == []:
        continue
    new_list_points_7.append(extra_points_7[i])
    new_list_coeffs_mod_N7.append(coeffs_mod_N7[i])

#Using logarithm:
L = Qp(p, 10)
_.<x> = PolynomialRing(L)
HQp = HyperellipticCurve(x^3 - 4)
M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp)
forms = [form.change_ring(L) for form in forms]
M_sys = matrix(L, M_frob).transpose() - 1
inverse_frob = M_sys**(-1)

LogQ1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi1(Q[0]), psi1(Q[1])), inverse_frob, forms)[0]
LogQ2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi2(Q[0]), psi2(Q[1])), inverse_frob, forms)[0]
LogR1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi1(R[0]), psi1(R[1])), inverse_frob, forms)[0]
LogR2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi2(R[0]), psi2(R[1])), inverse_frob, forms)[0]

M = Matrix([[LogQ1, LogR1], [LogQ2, LogR2]])
Minv = M^(-1)

coeffs_mod_7 = [[] for i in range(len(new_list_points_7))]
for i in range(len(new_list_points_7)):
    P = new_list_points_7[i]
    P1 = HQp(P[0][0], P[0][1])
    P2 = HQp(P[1][0], P[1][1])
    LogP1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), P1, inverse_frob, forms)[0]
    LogP2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), P2, inverse_frob, forms)[0]
    v = vector([LogP1, LogP2])
    vnm = Minv*v
    coeffs_mod_7[i].append([ZZ(vnm[0] % p), ZZ(vnm[1] % p)])


############## INFORMATION AT p = 13 ##############

p = 13
n = 20
p1, p2 = factor(p*OK)
p1 = (p1[0]^K.class_number()).gens_reduced()[0]
p2 = (p2[0]^K.class_number()).gens_reduced()[0]
EMBD1, EMBD2 = embeddings(K, p, n+5)

#These are the embeddings used in quad_chab_ell_im_quad
if EMBD1(p1).valuation() > 0:
    psi1 = EMBD1
    psi2 = EMBD2
else:
    psi1 = EMBD2
    psi2 = EMBD1
assert psi1(p1).valuation() > 0

Ep = E.change_ring(GF(p))
Q1 = Ep(psi1(Q[0])%p, psi1(Q[1])%p)
Q2 = Ep(psi2(Q[0])%p, psi2(Q[1])%p)
R1 = Ep(psi1(R[0])%p, psi1(R[1])%p)
R2 = Ep(psi2(R[0])%p, psi2(R[1])%p)
ord_1 = lcm(Q1.order(), Q2.order())
print "The order of Q in E(F_13) x E(F_13) is", ord_1
sys.stdout.flush()
ord_2 = lcm(R1.order(), R2.order())
print "The order of R in E(F_13) x E(F_13) is", ord_2
sys.stdout.flush()
coeffs_mod_N13 = [[] for i in range(len(extra_points_13))]
for i in range(len(extra_points_13)):
    P = extra_points_13[i]
    P1 = Ep(P[0][0], P[0][1])
    P2 = Ep(P[1][0], P[1][1])
    for n in range(ord_1):
        for m in range(ord_2):
            if n*Q1 + m*R1 == P1 and n*Q2 + m*R2 == P2:
                coeffs_mod_N13[i].append([n,m]) #n is modulo ord_1, m is modulo ord_2

new_list_points_13 = []
new_list_coeffs_mod_N13 = []

for i in range(len(extra_points_13)):
    if coeffs_mod_N13[i] == []:
        continue
    new_list_points_13.append(extra_points_13[i])
    new_list_coeffs_mod_N13.append(coeffs_mod_N13[i])

#Using logarithm:
L = Qp(p, 10)
_.<x> = PolynomialRing(L)
HQp = HyperellipticCurve(x^3 - 4)
M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp)
forms = [form.change_ring(L) for form in forms]
M_sys = matrix(L, M_frob).transpose() - 1
inverse_frob = M_sys**(-1)

LogQ1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi1(Q[0]), psi1(Q[1])), inverse_frob, forms)[0]
LogQ2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi2(Q[0]), psi2(Q[1])), inverse_frob, forms)[0]
LogR1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi1(R[0]), psi1(R[1])), inverse_frob, forms)[0]
LogR2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), HQp(psi2(R[0]), psi2(R[1])), inverse_frob, forms)[0]

M = Matrix([[LogQ1, LogR1],[LogQ2, LogR2]])
Minv = M^(-1)

coeffs_mod_13 = [[] for i in range(len(new_list_points_13))]
for i in range(len(new_list_points_13)):
    P = new_list_points_13[i]
    P1 = HQp(P[0][0], P[0][1])
    P2 = HQp(P[1][0], P[1][1])
    LogP1 = coleman_integrals_on_basis(HQp, HQp(0,1,0), P1, inverse_frob, forms)[0]
    LogP2 = coleman_integrals_on_basis(HQp, HQp(0,1,0), P2, inverse_frob, forms)[0]
    v = vector([LogP1, LogP2])
    vnm = Minv*v
    coeffs_mod_13[i].append([ZZ(vnm[0] % p), ZZ(vnm[1] % p)])


############## COMBINING INFORMATION AT 7 AND 13 ##############

number_points_to_get_rid_of = 0
remaining_points = []
remaining_points_res = []
for i in range(len(new_list_coeffs_mod_N13)):
    assert len(new_list_coeffs_mod_N13[i]) == 1
    mod_N13 = [[ZZ(new_list_coeffs_mod_N13[i][0][0] % 7), ZZ(new_list_coeffs_mod_N13[i][0][1] % 7)]]
    mod_13 = coeffs_mod_13[i]
    for j in range(len(new_list_coeffs_mod_N7)):
        assert len(new_list_coeffs_mod_N7[j]) == 1
        if new_list_coeffs_mod_N7[j] == mod_13 and coeffs_mod_7[j] == mod_N13 and new_list_points_7[j][2] == new_list_points_13[i][2]:
            remaining_points_res.append([mod_13,new_list_coeffs_mod_N13[i]])
            remaining_points.append([new_list_points_7[j],new_list_points_13[i]])
            number_points_to_get_rid_of += 1
print "%s points survived the sieve" %(number_points_to_get_rid_of)
sys.stdout.flush()
print "====================="
sys.stdout.flush()

remaining_points_reordered = []
remaining_points_reordered_res = []
for P in remaining_points:
    if P[0][0][0] == P[0][1][0] and P[1][0][0] == P[1][1][0]:
        remaining_points_reordered.append(P)
        remaining_points_reordered_res.append(remaining_points_res[remaining_points.index(P)])

for P in remaining_points:
    if P not in remaining_points_reordered:
        remaining_points_reordered.append(P)
        remaining_points_reordered_res.append(remaining_points_res[remaining_points.index(P)])

new_remaining_points = []
new_remaining_points_res = []
for P in remaining_points_reordered:
    par = 0
    for T in new_remaining_points:
        if (T[0][0][0]/P[0][0][0])^3 == 1 and (T[1][0][0]/P[1][0][0])^3 == 1 and ((T[0][0][1] - P[0][0][1] == 0 and T[1][0][1] - P[1][0][1] == 0) or  (T[0][0][1] + P[0][0][1] == 0 and T[1][0][1] + P[1][0][1] == 0)) and T[0][0][0]/P[0][0][0] + T[0][1][0]/P[0][1][0] == -1 and  T[1][0][0]/P[1][0][0] + T[1][1][0]/P[1][1][0] == -1:
            par = 1
            continue
    if par == 0:
        new_remaining_points.append(P)
        new_remaining_points_res.append(remaining_points_res[remaining_points.index(P)])

print "Number of automorphisms classes that survived the sieve:", len(new_remaining_points)
sys.stdout.flush()
print "====================="
sys.stdout.flush()
