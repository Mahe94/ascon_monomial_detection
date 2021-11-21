#!/usr/local/bin/sage
from sage.all import *

def get_bin(byte, N):
	X = []
	for i in range(N):
		t = (byte >> (N-1-i)) & 1
		X.append(t)
	return X

V = PolynomialRing(ZZ, 256,['k%d'%(i) for i in range(128)]+['v%d'%(i) for i in range(128)] )
V.inject_variables()

KEY = ['k%d'%i for i in range(128)]
NONCE = ['v%d'%i for i in range(128)]
IV = get_bin(0x80400c0600000000, 64)
X0 = IV 
X1 = [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63]
X2 = [k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, k81, k82, k83, k84, k85, k86, k87, k88, k89, k90, k91, k92, k93, k94, k95, k96, k97, k98, k99, k100, k101, k102, k103, k104, k105, k106, k107, k108, k109, k110, k111, k112, k113, k114, k115, k116, k117, k118, k119, k120, k121, k122, k123, k124, k125, k126, k127]
X3 = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63]
X4 = [v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127]
RC = [0xF0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b]


#####################
#
# $ nonce_full_monomial = prod_{i \in I} vi $	
# where I are the cube indices. This will be used to reduce an $vi^2$ term to $vi$ in the
# function "linearlize"
#
#####################
nonce_full_monomial = 1
for i in range(15):
	nonce_full_monomial = nonce_full_monomial*V.gens_dict()['v%d'%(i)]


#####################
#
# save_state stores the polynomials in the state (X0, X1, X2, X3, X4) into a file
# which can be retreived in the future
#
#####################
def save_state(X0, X1, X2, X3, X4, path, round):
	for i in range(64):
		X0[i].save(path + 'X_' + str(round) + '[0][' + str(i) + ']')
		X1[i].save(path + 'X_' + str(round) + '[1][' + str(i) + ']')
		X2[i].save(path + 'X_' + str(round) + '[2][' + str(i) + ']')
		X3[i].save(path + 'X_' + str(round) + '[3][' + str(i) + ']')
		X4[i].save(path + 'X_' + str(round) + '[4][' + str(i) + ']')
	return (X0, X1, X2, X3, X4)

#####################
#
# load_state loads the polynomials from a file to the variables (X0, X1, X2, X3, X4)
#
##################### 
def load_state(X0, X1, X2, X3, X4, path, round):
        for i in range(64):
                X0[i] = load(path + 'X_' + str(round) + '[0][' + str(i) + ']')
                X1[i] = load(path + 'X_' + str(round) + '[1][' + str(i) + ']')
                X2[i] = load(path + 'X_' + str(round) + '[2][' + str(i) + ']')
                X3[i] = load(path + 'X_' + str(round) + '[3][' + str(i) + ']')
                X4[i] = load(path + 'X_' + str(round) + '[4][' + str(i) + ']')
	return (X0, X1, X2, X3, X4)

#####################
#
# linearize function takes as input a polynomial p and degree bound deg and return another
# polynomial q such that q = p mod vi^2 - vi and the degree of every monomial is q is at
# least deg
#
#####################

def linearize(p, deg):
	temp = 0*v0
	for m in p.monomials():
		q = nonce_full_monomial.gcd(m) # gcd help in performing mod vi^2 - vi for all i
		if q.degree() >= deg:
			temp = temp + q
	return temp	

#####################
#
# permuation_wth_key_variables first computes the exact polynomials (in terms of keys 
# and cube varibles) of the state of "rounds"-round ASCON, but the polynomials are 
# computed over Z. Therefore, we must reduce the polynomial modulo 2 and modulo vi^2 - vi and
# modulo ki^2 - ki. Then, it return a polynomials in cube variable such that if a monomial m
# exists in the final polynomial then p.m exists in the original polynomial where p is a 
# polynomial with key variables only
#
#####################
def permutation_with_key_variables(X0, X1, X2, X3, X4, rounds):

	for r in range(rounds):

	# Addition of constant
		T = get_bin(RC[r], 8)
		for i in range(8):
			X2[56 + i] = X2[56 + i] + T[i]

	# Sbox layer
		for i in range(64):
			x0 = X0[i]
			x1 = X1[i]
			x2 = X2[i]
			x3 = X3[i]
			x4 = X4[i]
			X0[i] = x4*x1 + x3 + x2*x1 + x2 + x1*x0 + x1 + x0
			X1[i] = x4 + x3*x2 + x3*x1 + x3 + x2*x1 + x2 + x1 + x0
			X2[i] = x4*x3 + x4 + x2 + x1 + 1
			X3[i] = x4*x0 + x4 + x3*x0 + x3 + x2 + x1 + x0
			X4[i] = x4*x1 + x4 + x3 + x1*x0 + x1

	
		
		A0 = X0 
		A1 = X0[-19:] + X0[:-19]
		A2 = X0[-28:] + X0[:-28]

		B0 = X1 
		B1 = X1[-61:] + X1[:-61]
		B2 = X1[-39:] + X1[:-39]

		C0 = X2 
		C1 = X2[-1:] + X2[:-1]
		C2 = X2[-6:] + X2[:-6]

		D0 = X3 
		D1 = X3[-10:] + X3[:-10]
		D2 = X3[-17:] + X3[:-17]

		E0 = X4 
		E1 = X4[-7:] + X4[:-7]
		E2 = X4[-41:] + X4[:-41]

	
	

	# Linear layer
		
		for i in range(64):
			X0[i] = A0[i] + A1[i] + A2[i] 
			X1[i] = B0[i] + B1[i] + B2[i] 
			X2[i] = C0[i] + C1[i] + C2[i] 
			X3[i] = D0[i] + D1[i] + D2[i] 
			X4[i] = E0[i] + E1[i] + E2[i] 
	


	# I = <2>
	I = Ideal([v0*0 + Integer(2)])

	# full_monomial = \prod_{i \in [128]} ki \prod_{j \in I} vi
	full_monomial = 1
	for i in range(128):
		full_monomial = full_monomial*V.gens_dict()['k%d'%(i)]
	for i in range(15):
		full_monomial = full_monomial*V.gens_dict()['v%d'%(i)]
	print("Finished initializing fullmonomial and I")


	for i in range(64):
		print(i)
		Monomials = X0[i].monomials()
		Coefficients = X0[i].coefficients()
		temp = 0*v0
		for j in range(len(Monomials)):
			g = full_monomial.gcd(Monomials[j]) #performing vi^2-vi and ki^2-ki
			temp = temp + Coefficients[j]*g #this step is necessary because many monomials will be cancelled if we consider F_2 ring
		X0[i] = temp.reduce(I) #performing mod 2
		# In this step, we remove the key variables by setting then to 1
		X0[i] = X0[i](k0=1, k1=1, k2=1, k3=1, k4=1, k5=1, k6=1, k7=1, k8=1, k9=1, k10=1, k11=1, k12=1, k13=1, k14=1, k15=1, k16=1, k17=1, k18=1, k19=1, k20=1, k21=1, k22=1, k23=1, k24=1, k25=1, k26=1, k27=1, k28=1, k29=1, k30=1, k31=1, k32=1, k33=1, k34=1, k35=1, k36=1, k37=1, k38=1, k39=1, k40=1, k41=1, k42=1, k43=1, k44=1, k45=1, k46=1, k47=1, k48=1, k49=1, k50=1, k51=1, k52=1, k53=1, k54=1, k55=1, k56=1, k57=1, k58=1, k59=1, k60=1, k61=1, k62=1, k63=1, k64=1, k65=1, k66=1, k67=1, k68=1, k69=1, k70=1, k71=1, k72=1, k73=1, k74=1, k75=1, k76=1, k77=1, k78=1, k79=1, k80=1, k81=1, k82=1, k83=1, k84=1, k85=1, k86=1, k87=1, k88=1, k89=1, k90=1, k91=1, k92=1, k93=1, k94=1, k95=1, k96=1, k97=1, k98=1, k99=1, k100=1, k101=1, k102=1, k103=1, k104=1, k105=1, k106=1, k107=1, k108=1, k109=1, k110=1, k111=1, k112=1, k113=1, k114=1, k115=1, k116=1, k117=1, k118=1, k119=1, k120=1, k121=1, k122=1, k123=1, k124=1, k125=1, k126=1, k127=1)
		temp = 0*v0
		# We cannot perform mod 2 because it will destroy a lot of information about
		# the mononimals that exists in the original. Therefore, we simply iterate over
		# all the monomials and replace their coefficient with 1 (replacement is done by)
		# simply addition operation because monomials() function just returns the monomials
		# present in the polynomial.
		for m in X0[i].monomials():
			temp = temp + m
		X0[i] = temp
		print("Done with X0")



		Monomials = X1[i].monomials()
                Coefficients = X1[i].coefficients()
                temp = 0*v0
                for j in range(len(Monomials)):
                        g = full_monomial.gcd(Monomials[j])
                        temp = temp + Coefficients[j]*g
		X1[i] = temp.reduce(I)
                X1[i] = X1[i](k0=1, k1=1, k2=1, k3=1, k4=1, k5=1, k6=1, k7=1, k8=1, k9=1, k10=1, k11=1, k12=1, k13=1, k14=1, k15=1, k16=1, k17=1, k18=1, k19=1, k20=1, k21=1, k22=1, k23=1, k24=1, k25=1, k26=1, k27=1, k28=1, k29=1, k30=1, k31=1, k32=1, k33=1, k34=1, k35=1, k36=1, k37=1, k38=1, k39=1, k40=1, k41=1, k42=1, k43=1, k44=1, k45=1, k46=1, k47=1, k48=1, k49=1, k50=1, k51=1, k52=1, k53=1, k54=1, k55=1, k56=1, k57=1, k58=1, k59=1, k60=1, k61=1, k62=1, k63=1, k64=1, k65=1, k66=1, k67=1, k68=1, k69=1, k70=1, k71=1, k72=1, k73=1, k74=1, k75=1, k76=1, k77=1, k78=1, k79=1, k80=1, k81=1, k82=1, k83=1, k84=1, k85=1, k86=1, k87=1, k88=1, k89=1, k90=1, k91=1, k92=1, k93=1, k94=1, k95=1, k96=1, k97=1, k98=1, k99=1, k100=1, k101=1, k102=1, k103=1, k104=1, k105=1, k106=1, k107=1, k108=1, k109=1, k110=1, k111=1, k112=1, k113=1, k114=1, k115=1, k116=1, k117=1, k118=1, k119=1, k120=1, k121=1, k122=1, k123=1, k124=1, k125=1, k126=1, k127=1)
                temp = 0*v0
                for m in X1[i].monomials():
                        temp = temp + m
                X1[i] = temp
		print("Done with X1")



		Monomials = X2[i].monomials()
                Coefficients = X2[i].coefficients()
                temp = 0*v0
                for j in range(len(Monomials)):
                        g = full_monomial.gcd(Monomials[j])
                        temp = temp + Coefficients[j]*g
		X2[i] = temp.reduce(I)
                X2[i] = X2[i](k0=1, k1=1, k2=1, k3=1, k4=1, k5=1, k6=1, k7=1, k8=1, k9=1, k10=1, k11=1, k12=1, k13=1, k14=1, k15=1, k16=1, k17=1, k18=1, k19=1, k20=1, k21=1, k22=1, k23=1, k24=1, k25=1, k26=1, k27=1, k28=1, k29=1, k30=1, k31=1, k32=1, k33=1, k34=1, k35=1, k36=1, k37=1, k38=1, k39=1, k40=1, k41=1, k42=1, k43=1, k44=1, k45=1, k46=1, k47=1, k48=1, k49=1, k50=1, k51=1, k52=1, k53=1, k54=1, k55=1, k56=1, k57=1, k58=1, k59=1, k60=1, k61=1, k62=1, k63=1, k64=1, k65=1, k66=1, k67=1, k68=1, k69=1, k70=1, k71=1, k72=1, k73=1, k74=1, k75=1, k76=1, k77=1, k78=1, k79=1, k80=1, k81=1, k82=1, k83=1, k84=1, k85=1, k86=1, k87=1, k88=1, k89=1, k90=1, k91=1, k92=1, k93=1, k94=1, k95=1, k96=1, k97=1, k98=1, k99=1, k100=1, k101=1, k102=1, k103=1, k104=1, k105=1, k106=1, k107=1, k108=1, k109=1, k110=1, k111=1, k112=1, k113=1, k114=1, k115=1, k116=1, k117=1, k118=1, k119=1, k120=1, k121=1, k122=1, k123=1, k124=1, k125=1, k126=1, k127=1)
                temp = 0*v0
                for m in X2[i].monomials():
                        temp = temp + m
                X2[i] = temp
		print("Done with X2")



		Monomials = X3[i].monomials()
                Coefficients = X3[i].coefficients()
                temp = 0*v0
                for j in range(len(Monomials)):
                        g = full_monomial.gcd(Monomials[j])
                        temp = temp + Coefficients[j]*g
		X3[i] = temp.reduce(I)
                X3[i] = X3[i](k0=1, k1=1, k2=1, k3=1, k4=1, k5=1, k6=1, k7=1, k8=1, k9=1, k10=1, k11=1, k12=1, k13=1, k14=1, k15=1, k16=1, k17=1, k18=1, k19=1, k20=1, k21=1, k22=1, k23=1, k24=1, k25=1, k26=1, k27=1, k28=1, k29=1, k30=1, k31=1, k32=1, k33=1, k34=1, k35=1, k36=1, k37=1, k38=1, k39=1, k40=1, k41=1, k42=1, k43=1, k44=1, k45=1, k46=1, k47=1, k48=1, k49=1, k50=1, k51=1, k52=1, k53=1, k54=1, k55=1, k56=1, k57=1, k58=1, k59=1, k60=1, k61=1, k62=1, k63=1, k64=1, k65=1, k66=1, k67=1, k68=1, k69=1, k70=1, k71=1, k72=1, k73=1, k74=1, k75=1, k76=1, k77=1, k78=1, k79=1, k80=1, k81=1, k82=1, k83=1, k84=1, k85=1, k86=1, k87=1, k88=1, k89=1, k90=1, k91=1, k92=1, k93=1, k94=1, k95=1, k96=1, k97=1, k98=1, k99=1, k100=1, k101=1, k102=1, k103=1, k104=1, k105=1, k106=1, k107=1, k108=1, k109=1, k110=1, k111=1, k112=1, k113=1, k114=1, k115=1, k116=1, k117=1, k118=1, k119=1, k120=1, k121=1, k122=1, k123=1, k124=1, k125=1, k126=1, k127=1)
                temp = 0*v0
                for m in X3[i].monomials():
                        temp = temp + m
                X3[i] = temp
		print("Done with X3")



		Monomials = X4[i].monomials()
                Coefficients = X4[i].coefficients()
                temp = 0*v0
                for j in range(len(Monomials)):
                        g = full_monomial.gcd(Monomials[j])
                        temp = temp + Coefficients[j]*g
		X4[i] = temp.reduce(I)
                X4[i] = X4[i](k0=1, k1=1, k2=1, k3=1, k4=1, k5=1, k6=1, k7=1, k8=1, k9=1, k10=1, k11=1, k12=1, k13=1, k14=1, k15=1, k16=1, k17=1, k18=1, k19=1, k20=1, k21=1, k22=1, k23=1, k24=1, k25=1, k26=1, k27=1, k28=1, k29=1, k30=1, k31=1, k32=1, k33=1, k34=1, k35=1, k36=1, k37=1, k38=1, k39=1, k40=1, k41=1, k42=1, k43=1, k44=1, k45=1, k46=1, k47=1, k48=1, k49=1, k50=1, k51=1, k52=1, k53=1, k54=1, k55=1, k56=1, k57=1, k58=1, k59=1, k60=1, k61=1, k62=1, k63=1, k64=1, k65=1, k66=1, k67=1, k68=1, k69=1, k70=1, k71=1, k72=1, k73=1, k74=1, k75=1, k76=1, k77=1, k78=1, k79=1, k80=1, k81=1, k82=1, k83=1, k84=1, k85=1, k86=1, k87=1, k88=1, k89=1, k90=1, k91=1, k92=1, k93=1, k94=1, k95=1, k96=1, k97=1, k98=1, k99=1, k100=1, k101=1, k102=1, k103=1, k104=1, k105=1, k106=1, k107=1, k108=1, k109=1, k110=1, k111=1, k112=1, k113=1, k114=1, k115=1, k116=1, k117=1, k118=1, k119=1, k120=1, k121=1, k122=1, k123=1, k124=1, k125=1, k126=1, k127=1)
                temp = 0*v0
                for m in X4[i].monomials():
                        temp = temp + m
                X4[i] = temp
		print("Done with X4")

	
	return (X0, X1, X2, X3, X4)

#####################
#
# permuation takes polynomial in cube variable and perform ASCON permuation starting
# from "pre_rounds" round to "rounds" round. After each round, it perform mod 2 operation.
#
#####################
def permutation(X0, X1, X2, X3, X4, pre_rounds, rounds):
			
	for r in range(pre_rounds, rounds):

        # Addition of constant
                T = get_bin(RC[r], 8)
                for i in range(8):
                        X2[56 + i] = X2[56 + i] + T[i]

        # Sbox layer
                for i in range(64):
                        x0 = X0[i]
                        x1 = X1[i]
                        x2 = X2[i]
                        x3 = X3[i]
                        x4 = X4[i]
                        X0[i] = x4*x1 + x3 + x2*x1 + x2 + x1*x0 + x1 + x0
                        X1[i] = x4 + x3*x2 + x3*x1 + x3 + x2*x1 + x2 + x1 + x0
                        X2[i] = x4*x3 + x4 + x2 + x1 + 1
                        X3[i] = x4*x0 + x4 + x3*x0 + x3 + x2 + x1 + x0
                        X4[i] = x4*x1 + x4 + x3 + x1*x0 + x1



                A0 = X0
                A1 = X0[-19:] + X0[:-19]
                A2 = X0[-28:] + X0[:-28]

                B0 = X1
                B1 = X1[-61:] + X1[:-61]
                B2 = X1[-39:] + X1[:-39]

                C0 = X2
                C1 = X2[-1:] + X2[:-1]
                C2 = X2[-6:] + X2[:-6]

                D0 = X3
                D1 = X3[-10:] + X3[:-10]
                D2 = X3[-17:] + X3[:-17]

                E0 = X4
                E1 = X4[-7:] + X4[:-7]
                E2 = X4[-41:] + X4[:-41]




        # Linear layer

                for i in range(64):
                        X0[i] = A0[i] + A1[i] + A2[i]
                        X1[i] = B0[i] + B1[i] + B2[i]
                        X2[i] = C0[i] + C1[i] + C2[i]
                        X3[i] = D0[i] + D1[i] + D2[i]
                        X4[i] = E0[i] + E1[i] + E2[i]
		
		#val = int(raw_input("Do you want to reduce the polynomials:"))
		if r == pre_rounds:
			full_monomial = 1
			for i in range(15):
				full_monomial = full_monomial*V.gens_dict()['v%d'%(i)]
			for i in range(64):
				print(i)
				temp = 0*v0
				for m in X0[i].monomials():
					temp = temp + full_monomial.gcd(m) # mod 2 and mod vi^2-vi
				X0[i] = temp
				print("Done with X0")


				temp = 0*v0
        	                for m in X1[i].monomials():
                	                temp = temp + full_monomial.gcd(m)
                        	X1[i] = temp
                       		print("Done with X1")


				temp = 0*v0
        	                for m in X2[i].monomials():
	                                temp = temp + full_monomial.gcd(m)
	                        X2[i] = temp
        	                print("Done with X2")


				temp = 0*v0
                        	for m in X3[i].monomials():
                                	temp = temp + full_monomial.gcd(m)
	                        X3[i] = temp
	                        print("Done with X3")


				temp = 0*v0
	                        for m in X4[i].monomials():
        	                        temp = temp + full_monomial.gcd(m)
                	        X4[i] = temp
                        	print("Done with X4")
			

	return (X0, X1, X2, X3, X4)

# Set X4 = X3

for i in range(64):
	X4[i] = 0

for i in range(15, 64):
	X3[i] = 0

for i in range(15):
	X4[i] = V.gens_dict()['v%d'%(i)]


#r = int(raw_input("Enter number of rounds:"))
(X0, X1, X2, X3, X4) = permutation_with_key_variables(X0, X1, X2, X3, X4, 2)
(X0, X1, X2, X3, X4) = permutation(X0, X1, X2, X3, X4, 2, 4)

print("Completed 4 rounds")

#####################
# since performing mod vi^2 -vi is time consuming for the final round, we will optimize it
# by reducing polynomial at few indices. If we consider the 1st indices of X_0^5, it is 
# depended on X_0^4[1, -18, -27], X_1^4[1, -18, -27], X_2^4[1, -18, -27] and X_4^4[1, -18, -27].
# Therefore, we perfoming the reduction only on these indices. Also, it suffices to keep only
# high order monomials.
#####################

y0_1 = linearize(X0[1], 6)
y1_1 = linearize(X1[1], 6)
y2_1 = linearize(X2[1], 6)
y4_1 = linearize(X4[1], 6)

y0_18 = linearize(X0[-18], 6)
y1_18 = linearize(X1[-18], 6)
y2_18 = linearize(X2[-18], 6)
y4_18 = linearize(X4[-18], 6)

y0_27 = linearize(X0[-27], 6)
y1_27 = linearize(X1[-27], 6)
y2_27 = linearize(X2[-27], 6)
y4_27 = linearize(X4[-27], 6)

sum_y_1 = y0_1 + y2_1 + y4_1
sum_y_18 = y0_18 + y2_18 + y4_18
sum_y_27 = y0_27 + y2_27 + y4_27

final_polynomial_1 = linearize(linearize(y1_1, 7) * linearize(sum_y_1, 7), 14) + linearize(linearize(y1_1, 8) * linearize(sum_y_1, 6), 14)
final_polynomial_18 = linearize(linearize(y1_18, 7) * linearize(sum_y_18, 7), 14) + linearize(linearize(y1_18, 8) * linearize(sum_y_18, 6), 14)
final_polynomial_27 = linearize(linearize(y1_27, 7) * linearize(sum_y_27, 7), 14) + linearize(linearize(y1_27, 8) * linearize(sum_y_27, 6), 14)
print(final_polynomial_1 + final_polynomial_18 + final_polynomial_27)
print("\n")

#for i in range(64):
	#print(str(i) + "\n")
	#print(X0[i])
	#print("\n\n")
	#print(X1[i])
	#print("\n")
	#print(X2[i])
	#print("\n")
	#print(X3[i])
	#print("\n")
	#print(X4[i])
	

#raw_input()
#for i in range(64):
#        print(str(i) + "\n")
#        print(X1[i])
#        print("\n\n")
