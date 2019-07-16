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
    sumBitDecomp.in <-- sum;
    for (var i = 0; i < w; i++) {
        sumBitDecomp.out[i] --> sumBits[i];
    }

    component carryBitDecomp = Num2Bits(2);
    carryBitDecomp.in <-- carry;
    for (var i = 0; i < 2; i++) {
        carryBitDecomp.out[i] --> carryBits[i];
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
