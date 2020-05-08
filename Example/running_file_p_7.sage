K.<a> = QuadraticField(-3)
E = EllipticCurve([0,-4])
int_points = [(-61*a + 61 , -778*a ),(61*a + 61 , 778*a ),(5 , 11 ),(3*a - 5 , 4*a + 18 ),(-3*a - 5 , -4*a + 18 ),(1/2*(-5*a - 5) , -11 ),(4*a - 2 , 4*a - 18 ), (1/2*(a - 1) , -a ),(2 , -2 ),(1/2*(-a - 1) , a ),(-4*a - 2 , -4*a - 18 ),(1/2*(5*a - 5) , -11 ),(a + 7 , -4*a - 18 ),(-a - 1 , 2 ),(-a + 1 , -2*a ),(a + 1 , 2*a ),(a - 1 , 2 ),(-a + 7 , 4*a - 18 ),(-122 , 778*a ),(1 , a ),(-2 , 2*a ),(-2 , -2*a ),(1 , -a ),(-122 , -778*a ),(-a + 7 , -4*a + 18 ),(a - 1 , -2 ),(a + 1 , -2*a ),(-a + 1 , 2*a ),(-a - 1 , -2 ),(a + 7 , 4*a + 18 ),(1/2*(5*a - 5) , 11 ),(-4*a - 2 , 4*a + 18 ),(1/2*(-a - 1) , -a ),(2 , 2 ),(1/2*(a - 1) , a ),(4*a - 2 , -4*a + 18),(1/2*(-5*a - 5) , 11 ),(-3*a - 5 , 4*a - 18 ),(3*a - 5 , -4*a - 18 ),(5 , -11 ),(61*a + 61 , -778*a ),(-61*a + 61 , 778*a )]
A = quad_chab_ell_im_quad(E, 7, 20, 5, K, int_list = int_points, bernardi = False)

print "-----------"
sys.stdout.flush()
print "Number of discs for which double roots were unresolved:", A[4]
sys.stdout.flush()
print "-----------"
sys.stdout.flush()
print "Q-integral points recovered:", A[0]
sys.stdout.flush()
print "-----------"
sys.stdout.flush()
print "Other integral points recovered:", A[1]
sys.stdout.flush()
print "-----------"
sys.stdout.flush()
if len(A[0]) + len(A[1]) == len(int_points):
    ans = "No"
else:
    ans = "Yes"
print "Is the number of points recognised as integral larger than the number of known integral points?", ans
sys.stdout.flush()
print "-----------"
sys.stdout.flush()

extra_points_7 = A[2] + A[3]

print "extra_points_7:"
sys.stdout.flush()
print extra_points_7
sys.stdout.flush()
