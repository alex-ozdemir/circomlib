include "../bitify.circom";

template FullAdder(w) {
    // An adder which adds 3 w-bit numbers and produces:
    // * a w-bit result and
    // * a w-bit carry
    //
    signal input in1;
    signal input in2;
    signal input in3;

    signal output sum;
    signal output carry;
    signal output sumBits[w];
    signal output carryBits[2];

    signal rawSum;

    rawSum <== in1 + in2 + in3;

    carry <-- rawSum >> w;
    sum <-- rawSum % (2 ** w);
    rawSum === carry * 2 ** w + sum;

    component sumBitDecomp = Num2Bits(w);
    sumBitDecomp.in <== sum;
    for (var i = 0; i < w; i++) {
        sumBitDecomp.out[i] ==> sumBits[i];
    }

    component carryBitDecomp = Num2Bits(2);
    carryBitDecomp.in <== carry;
    for (var i = 0; i < 2; i++) {
        carryBitDecomp.out[i] ==> carryBits[i];
    }
}

template RippleCarryAdder(w, nWords) {
    // An adder which adds two nWords-word numbers of w-bit words together.

    signal input a[nWords];
    signal input b[nWords];

    signal output sum[nWords + 1];
    signal carry[nWords + 1];

    carry[0] <== 0;

    component adder[nWords];
    for (var i = 0; i < nWords; ++i) {
        adder[i] = FullAdder(w);
        adder[i].in1 <== carry[i];
        adder[i].in2 <== a[i];
        adder[i].in3 <== b[i];
        adder[i].sum ==> sum[i];
        adder[i].carry ==> carry[i + 1];
    }

    sum[nWords] <== carry[nWords];
}

template WordMultiplier(w) {
    signal input a;
    signal input b;

    signal output carry;
    signal output prod;

    signal rawProduct;

    rawProduct <== a * b;
    carry <-- rawProduct >> w;
    prod <-- rawProduct % (2 ** w);
    rawProduct === carry * 2 ** w + prod;

    component prodBitDecomp = Num2Bits(w);
    prodBitDecomp.in <== prod;

    component carryBitDecomp = Num2Bits(w);
    carryBitDecomp.in <== carry;

}

template WordMultiplierWithCarry(w) {
    // Requires w > 1
    signal input a;
    signal input b;
    signal input carryIn1;
    signal input carryIn2;

    signal output carryOut;
    signal output prod;

    signal rawProduct;

    rawProduct <== a * b + carryIn1 + carryIn2;
    carryOut <-- rawProduct >> w;
    prod <-- rawProduct % (2 ** w);
    rawProduct === carryOut * 2 ** w + prod;

    component prodBitDecomp = Num2Bits(w);
    prodBitDecomp.in <== prod;

    component carryBitDecomp = Num2Bits(w);
    carryBitDecomp.in <== carryOut;
}

template NBy1MultiplierAndAdder(w, n) {
    // prod = a * b + c

    signal input a[n];
    signal input b;

    signal input c[n];

    signal output prod[n+1];

    signal carry[n + 1];

    carry[0] <== 0;

    component wordMultiplier[n];
    for (var i = 0; i < n; ++i) {
        wordMultiplier[i] = WordMultiplierWithCarry(w);
        wordMultiplier[i].a <== a[i];
        wordMultiplier[i].b <== b;
        wordMultiplier[i].carryIn1 <== carry[i];
        wordMultiplier[i].carryIn2 <== c[i];
        wordMultiplier[i].carryOut ==> carry[i+1];
        wordMultiplier[i].prod ==> prod[i];
    }

    carry[n] ==> prod[n];
}

template Multiplier(w, n) {
    // An multiplier for two n-word numbers of w-bit words.

    signal input a[n];
    signal input b[n];

    signal output prod[2 * n];

    signal lineProds[n][n + 1];
    component lineMultipliers[n];

    for (var bi = 0; bi < n; bi++) {
        lineMultipliers[bi] = NBy1MultiplierAndAdder(w, n);
        for (var ai = 0; ai < n; ai++) {
            lineMultipliers[bi].a[ai] <== a[ai];
            if (bi > 0) {
                lineMultipliers[bi].c[ai] <== lineProds[bi - 1][ai + 1];
            } else {
                lineMultipliers[bi].c[ai] <== 0;
            }
        }
        lineMultipliers[bi].b <== b[bi];
        for (var ai = 0; ai < n + 1; ai++) {
            lineMultipliers[bi].prod[ai] ==> lineProds[bi][ai];
        }
    }
    for (var i = 0; i < n; i++) {
        prod[i] <== lineProds[i][0];
    }
    for (var i = 1; i < n + 1; i++) {
        prod[n - 1 + i] <== lineProds[n - 1][i];
    }
}

template PolynomialMultiplier(d) {
    // Implementation of _xjSnark_'s multiplication.
    // Polynomials with degree less than d.
    // Uses a linear number of constraints ($2n - 1$).
    // Based on the linear indepedence of $2n - 1$ equations.
    //
    // $x$ is `a`
    // $y$ is `b`
    signal input a[d];
    signal input b[d];

    // Witness value.
    signal output prod[2 * d - 1];

    // Witness computation.
    compute {
        var acc;
        for (var i = 0; i < 2 * d - 1; i++) {
            acc = 0;
            for (var j = 0; j < d; j++) {
                for (var k = 0; k < d; k++) {
                    if (j + k == i) {
                        acc += a[j] * b[k];
                    }
                }
            }
            prod[i] <-- acc;
        }
    }

    // Conditions.
    var aAcc;
    var bAcc;
    var pAcc;
    for (var c = 0; c < 2 * d - 1; c++) {
        aAcc = 0;
        bAcc = 0;
        pAcc = 0;
        for (var i = 0; i < d; i++) {
            aAcc += (c + 1) ** i * a[i];
            bAcc += (c + 1) ** i * b[i];
        }
        for (var i = 0; i < 2 * d - 1; i++) {
            pAcc += (c + 1) ** i * prod[i];
        }
        aAcc * bAcc === pAcc;
    }
}

template Carry(w, n) {
    // Given a 2w-bit, n-word number
    // produces the (n+1)-word number w-bit chunks.
    // Asserts that the number actually fits in (n+1) words.
    //
    // Uses $(2n+1)(w+1)$ constraints
    signal input in[n];

    signal output out[n+1];

    component outBitDecomps[n+1];
    component carryBitDecomps[n];

    signal carry[n+1];

    carry[0] <== 0;

    for (var i = 0; i < n; i++) {
        out[i] <-- (in[i] + carry[i]) % (2 ** w);
        carry[i + 1] <-- (in[i] + carry[i]) \ (2 ** w);

        // Verify we've split correctly
        carry[i + 1] * (2 ** w) + out[i] === carry[i] + in[i];

        // Verify our parts fit in w bits.
        outBitDecomps[i] = Num2Bits(w);
        outBitDecomps[i].in <== out[i];
        carryBitDecomps[i] = Num2Bits(w + 1);
        carryBitDecomps[i].in <== carry[i + 1];
    }

    // The final carry is our final word
    out[n] <== carry[n];
}

template CarriesToZero(w, n) {
    // Given a 2w-bit, n-word number, verifies that after carries it is 0.
    // Uses ~n(w+2) constraints.
    signal input in[n];

    component carryBitDecomps[n - 1];

    signal carry[n + 1];

    carry[0] <== 0;

    for (var i = 0; i < n; i++) {
        carry[i + 1] <-- (in[i] + carry[i]) \ (2 ** w);

        // Verify we've split correctly
        carry[i + 1] * (2 ** w) === carry[i] + in[i];

        // Verify our parts fit in w bits.
        if (i < n - 1) {
            carryBitDecomps[i] = Num2Bits(w+1);
            carryBitDecomps[i].in <== carry[i + 1];
        } else {
            // The final carry is our final word -- must be zero
            carry[i + 1] === 0;
        }
    }

}

template LinearMultiplier(w, n) {
    // Implementation of _xjSnark_'s multiplication for n-word numbers.
    //
    // Uses $2n - 1$ constraints for polynomial multiplication.
    // Uses $2nw + n + w$ carrying
    // For a total of $2nw + 4n + w - 1$ constraints.

    signal input a[n];
    signal input b[n];

    signal output prod[2 * n];

    component polyMultiplier = PolynomialMultiplier(n);
    component carrier = Carry(w, 2 * n - 1);

    // Put our inputs into the polynomial multiplier
    for (var i = 0; i < n; i++) {
        polyMultiplier.a[i] <== a[i];
        polyMultiplier.b[i] <== b[i];
    }

    // Put the polynomial product into the carrier
    for (var i = 0; i < 2 * n - 1; i++) {
        carrier.in[i] <== polyMultiplier.prod[i];
    }

    // Take the carrier output as our own
    for (var i = 0; i < 2 * n; i++) {
        prod[i] <== carrier.out[i];
    }
}

template LinearMultiplierWithAdd(w, n) {
    // Implementation of _xjSnark_'s multiplication for n-word numbers.
    //
    //     a * b + c == prod
    //
    // Uses $2n - 1$ constraints for polynomial multiplication.
    // Uses $2n(w + 1)$ for bit decomposition of the result.
    // Uses $2n - 1$ constraints for bit decomposition.
    // For a total of $2nw + 4n + w - 1$ constraints.

    signal input a[n];
    signal input b[n];
    signal input c[n];

    signal output prod[2 * n];

    component polyMultiplier = PolynomialMultiplier(n);
    component carrier = Carry(w, 2 * n - 1);

    // Put our inputs into the polynomial multiplier
    for (var i = 0; i < n; i++) {
        polyMultiplier.a[i] <== a[i];
        polyMultiplier.b[i] <== b[i];
    }

    // Put the polynomial product into the carrier
    for (var i = 0; i < 2 * n - 1; i++) {
        if (i < n) {
            carrier.in[i] <== polyMultiplier.prod[i] + c[i];
        } else {
            carrier.in[i] <== polyMultiplier.prod[i];
        }
    }

    // Take the carrier output as our own
    for (var i = 0; i < 2 * n; i++) {
        prod[i] <== carrier.out[i];
    }
}

template Quotient(w, n) {
    // Asserts that the quotient actually requires w*n bits
    // $2n(w + 3) - 2$ constraints for the multiplier
    // Another bitdecomp for n * w, yields:
    //    $3n(w + 2) - 2$
    signal input dividend[2 * n];
    signal input divisor[n];
    signal output quotient[n];
    signal output remainder[n];

    compute {
        int dividendAcc = int(0);
        int divisorAcc = int(0);
        for (int i = int(0); i < int(2 * n); i++) {
            dividendAcc += int(dividend[i]) << (int(w) * i);
        }
        for (int i = int(0); i < int(n); ++i) {
            divisorAcc += int(divisor[i]) << (int(w) * i);
        }
        int quotientAcc = dividendAcc / divisorAcc;
        int remainderAcc = dividendAcc % divisorAcc;
        for (int i = int(0); i < int(n); ++i) {
            quotient[i] <-- field(quotientAcc % int(2 ** w));
            quotientAcc = quotientAcc >> int(w);
        }
        for (int i = int(0); i < int(n); ++i) {
            remainder[i] <-- field(remainderAcc % int(2 ** w));
            remainderAcc = remainderAcc >> int(w);
        }
        quotientAcc === int(0);
        remainderAcc === int(0);
    }

    component remainderDecomp[n];
    for (var i = 0; i < n; i++) {
        remainderDecomp[i] = Num2Bits(w);
        remainderDecomp[i].in <== remainder[i];
    }

    component multiplier = LinearMultiplierWithAdd(w, n);
    for (var i = 0; i < n; i++) {
        multiplier.a[i] <== quotient[i];
        multiplier.b[i] <== divisor[i];
        multiplier.c[i] <== remainder[i];
    }
    for (var i = 0; i < 2 * n; i++) {
        multiplier.prod[i] === dividend[i];
    }
}

template MultiplierReducer(w, n) {
    // Computes prod and verifies that `prod = a * b (mod modulus)
    // Constraints:
    //   2(2n - 1) for two polynomial multipliers
    //   (w + 1)(2(2n - 1) + 1) for a 2n-word carry
    //   Total:
    //      (w + 2)(4n - 1) - 1
    signal input a[n];
    signal input b[n];
    signal input modulus[n];

    signal quotient[n];

    signal output prod[n];

    compute {
        int aAcc = int(0);
        int bAcc = int(0);
        int mAcc = int(0);
        for (int i = int(0); i < int(n); i++) {
            aAcc += int(a[i]) << (int(w) * i);
            bAcc += int(b[i]) << (int(w) * i);
            mAcc += int(modulus[i]) << (int(w) * i);
        }
        int fullProdAcc = aAcc * bAcc;
        int quotientAcc = fullProdAcc / mAcc;
        int prodAcc = fullProdAcc % mAcc;

        for (int i = int(0); i < int(n); ++i) {
            quotient[i] <-- field(quotientAcc % int(2 ** w));
            quotientAcc = quotientAcc >> int(w);
        }
        for (int i = int(0); i < int(n); ++i) {
            prod[i] <-- field(prodAcc % int(2 ** w));
            prodAcc = prodAcc >> int(w);
        }

        quotientAcc === int(0);
        prodAcc === int(0);
    }

    // Verify that the remainder and quotient are w-bits, n-chunks.
    component prodDecomp[n];
    for (var i = 0; i < n; i++) {
        prodDecomp[i] = Num2Bits(w);
        prodDecomp[i].in <== prod[i];
    }

    component quotientDecomp[n];
    for (var i = 0; i < n; i++) {
        quotientDecomp[i] = Num2Bits(w);
        quotientDecomp[i].in <== quotient[i];
    }

    component left = PolynomialMultiplier(n);
    component right = PolynomialMultiplier(n);
    for (var i = 0; i < n; ++i) {
        left.a[i] <== a[i];
        left.b[i] <== b[i];
        right.a[i] <== quotient[i];
        right.b[i] <== modulus[i];
    }

    component carry = CarriesToZero(w, 2 * n - 1);
    for (var i = 0; i < 2 * n - 1; ++i) {
        if (i < n) {
            carry.in[i] <== left.prod[i] - right.prod[i] - prod[i];
        } else {
            carry.in[i] <== left.prod[i] - right.prod[i];
        }
    }
}
