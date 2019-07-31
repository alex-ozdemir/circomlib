include "../bitify.circom";

function log2(x) {
    for (var i = 0; i < x; ++i) {
        if (2 ** i >= x) {
            return i;
        }
    }
    return x;
}

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

    component outBitDecomps[n];
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

template EqualWhenCarried(wordMax, outWidth, n) {
    // Given two (overflowing) n-chunk integers asserts:
    //   that they fir properly in n+1 chunks AND
    //   that they're equal
    // Params:
    //   wordMax:   an upper bound on all input words
    //   outWidth:  the desired output width
    //   n:         the number of chunks in the inputs
    // Constraints:
    //   $n$ constraints for carry + output sums
    //   $(n-1)(ceil(log2(2wordMax)) - w)$ contraints for bit decompositions
    //
    //   $(n - 1)(ceil(log2(wordMax)) - w + 2) + 1$ in total

    // The naive approach is to add the two numbers chunk by chunk and:
    //    a. Verify that they sum to zero along the way while
    //    b. Propegating carries
    // but this doesn't work because early sums might be negative.
    // So instead we choose a special c and verify that a - b + c = c
    // where c is chosen to insure that intermediate sums are non-negative.

    signal input a[n];
    signal input b[n];

    component carryBitDecomps[n - 1];
    signal carry[n + 1];
    signal out[n];

    var carryBits = log2(2 * wordMax) - outWidth;
    var outBase = 2 ** outWidth;
    var accumulatedExtra = 0;

    carry[0] <== 0;

    for (var i = 0; i < n; i++) {
        // We add an extra (wordMax) to the carry to ensure that it is positive
        out[i] <--(a[i] - b[i] + carry[i] + wordMax) % outBase;

        carry[i + 1] <-- (a[i] - b[i] + carry[i] + wordMax) \ outBase;

        // Verify we've split correctly
        carry[i + 1] * outBase + out[i] === carry[i] + a[i] - b[i] + wordMax;

        // Verify that the output is correct
        accumulatedExtra += wordMax;
        out[i] === accumulatedExtra % outBase;
        accumulatedExtra = accumulatedExtra \ outBase;

        // Verify that our carry fits in `carryBits` bits
        if (i < n - 1) {
            carryBitDecomps[i] = Num2Bits(carryBits);
            carryBitDecomps[i].in <== carry[i + 1];
        } else {
            // The final carry should match the extra
            carry[i + 1] === accumulatedExtra;
        }
    }
}

template Regroup(w, n, g) {
    // Given base-w, n-chunk integers, regroups them such that up to g groups go together
    var nGroups = (n - 1) \ g + 1;
    signal input in[n];
    signal output out[nGroups];

    var lc[nGroups];
    for (var i = 0; i < nGroups; ++i) {
        lc[i] = 0;
        for (var j = 0; j < g && i * g + j < n; ++j) {
            lc[i] += (2 ** (w * j)) * in[i * g + j];
        }
        out[i] <== lc[i];
    }
}

template EqualWhenCarriedRegroup(wordMax, outWidth, n) {
    // Given two (overflowing) n-chunk integers asserts:
    //   that they fir properly in n+1 chunks AND
    //   that they're equal
    // Params:
    //   wordMax:   an upper bound on all input words
    //   outWidth:  the desired output width
    //   n:         the number of chunks in the inputs
    // Constraints:
    //   $(nGroups - 1)(ceil(log2(groupMax)) - outWidth + 2) + 1$
    //   ~
    //   $(ceil(n/chunksPerGroup) - 1)(ceil(log2(groupMax)) - w + 2) + 1$
    //   $(ceil(n/floor((252 - carryBits) / outWidth)) - 1)(ceil(log2(groupMax)) - w + 2) + 1$
    //   $(ceil(n/floor((251 - ceil(log2(wordMax)) + outWidth) / outWidth)) - 1)(ceil(log2(groupMax)) - w + 2) + 1$

    // The naive approach is to add the two numbers chunk by chunk and:
    //    a. Verify that they sum to zero along the way while
    //    b. Propegating carries
    // but this doesn't work because early sums might be negative.
    // So instead we choose a special c and verify that a - b + c = c
    // where c is chosen to insure that intermediate sums are non-negative.

    signal input a[n];
    signal input b[n];

    var carryBits = log2(2 * wordMax) - outWidth;
    var outBase = 2 ** outWidth;
    var chunksPerGroup = (252 - carryBits) \ outWidth;
    var nGroups = (n - 1) \ chunksPerGroup + 1;
    var groupMax = 0;
    for (var i = 0; i < chunksPerGroup; ++i) {
        groupMax += 2 ** (outWidth * i) * wordMax;
    }

    // Group a, b
    component aGrouper = Regroup(outWidth, n, chunksPerGroup);
    component bGrouper = Regroup(outWidth, n, chunksPerGroup);

    for (var i = 0; i < n; ++i) {
        aGrouper.in[i] <== a[i];
        bGrouper.in[i] <== b[i];
    }

    // Now, check carries
    component equality = EqualWhenCarried(groupMax, outWidth * chunksPerGroup, nGroups);


    for (var i = 0; i < nGroups; ++i) {
        equality.a[i] <== aGrouper.out[i];
        equality.b[i] <== bGrouper.out[i];
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

template MultiplierReducer(w, n) {
    // Computes prod and verifies that `prod = a * b (mod modulus)
    // Constraints:
    //   $2(2n - 1)$ for two polynomial multipliers
    //   $(2n - 2)(w + 2 + ceil(log2(2n - 1))) + 1$ for the carried equality
    //   $2(nw)$ for the product and modulus decompositions
    //   Total:
    //      2n(2w + ceil(log2(n)) + 5) - 2w - 7
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

    var maxWord = n * (2 ** w - 1) * (2 ** w - 1) + (2 ** w - 1);
    component carry = EqualWhenCarriedRegroup(maxWord, w, 2 * n - 1);
    for (var i = 0; i < 2 * n - 1; ++i) {
        if (i < n) {
            carry.a[i] <== left.prod[i];
            carry.b[i] <== right.prod[i] + prod[i];
        } else {
            carry.a[i] <== left.prod[i];
            carry.b[i] <== right.prod[i];
        }
    }
}

template PowerMod(w, nb, ne) {
    // Constraints:
    //    <= 2 * w * ne * (w + 2) * (4nb - 1)
    signal input base[nb];
    signal input exp[ne];

    signal input modulus[nb];
    signal output out[nb];

    component powerBinExp = PowerModBin(w, nb, ne * w);

    component expDecomp[ne];
    for (var i = 0; i < nb; ++i) {
        powerBinExp.base[i] <== base[i];
        powerBinExp.modulus[i] <== modulus[i];
    }
    for (var i = 0; i < ne; ++i) {
        expDecomp[i] = Num2Bits(w);
        expDecomp[i].in <== exp[i];
        for (var j = 0; j < w; ++j) {
            powerBinExp.binaryExp[i * w + j] <== expDecomp[i].out[j];
        }
    }
    for (var i = 0; i < nb; ++i) {
        out[i] <== powerBinExp.out[i];
    }
}

template PowerModBin(w, nb, bitsExp) {
    //
    // Constraints:
    //    2 * bitsExp * 2(2nw + 4n - w - 1)     for two multipliers per exp bit
    //    bitsExp * 1                           for one ternary per exp bit
    //    <= 4 * bitsExp * (2nw + 4n - w)       total
    signal input base[nb];
    signal input binaryExp[bitsExp];

    signal input modulus[nb];
    signal output out[nb];
    if (bitsExp == 0) {
        out[0] <== 1;
        for (var i = 1; i < nb; ++i) {
            out[i] <== 0;
        }
    } else {
        component recursive = PowerModBin(w, nb, bitsExp - 1);
        component square = MultiplierReducer(w, nb);
        component mult = MultiplierReducer(w, nb);
        for (var i = 0; i < nb; ++i) {
            square.modulus[i] <== modulus[i];
            square.a[i] <== base[i];
            square.b[i] <== base[i];
        }
        for (var i = 0; i < nb; ++i) {
            recursive.base[i] <== square.prod[i];
            recursive.modulus[i] <== modulus[i];
        }
        for (var i = 0; i < bitsExp - 1; ++i) {
            recursive.binaryExp[i] <== binaryExp[i + 1];
        }
        for (var i = 0; i < nb; ++i) {
            mult.modulus[i] <== modulus[i];
            mult.a[i] <== base[i];
            mult.b[i] <== recursive.out[i];
        }
        for (var i = 0; i < nb; ++i) {
            out[i] <== recursive.out[i] + binaryExp[0] * (mult.prod[i] - recursive.out[i]);
        }
    }
}
