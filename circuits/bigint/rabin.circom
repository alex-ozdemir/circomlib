include "./bigint.circom"

template MultiplierReducerWithAdd(w, n) {
    // Computes prod and verifies that `prod = a * b (mod modulus)
    // Constraints:
    //   $2(2n - 1)$ for two polynomial multipliers
    //   $((2n - 1) - 1)(w + 3) + 1$ for the carried equality
    //   $2(nw)$ for the product and modulus decompositions
    //   Total:
    //      2(2nw + 4n - w - 1)
    signal input a[n];
    signal input b[n];
    signal input c[n];
    signal input modulus[n];

    signal quotient[n];

    signal output prod[n];

    compute {
        int aAcc = int(0);
        int bAcc = int(0);
        int cAcc = int(0);
        int mAcc = int(0);
        for (int i = int(0); i < int(n); i++) {
            aAcc += int(a[i]) << (int(w) * i);
            bAcc += int(b[i]) << (int(w) * i);
            cAcc += int(c[i]) << (int(w) * i);
            mAcc += int(modulus[i]) << (int(w) * i);
        }
        int fullProdAcc = aAcc * bAcc + cAcc;
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

    component carry = EqualWhenCarried(w, 2 * n - 1);
    for (var i = 0; i < 2 * n - 1; ++i) {
        if (i < n) {
            carry.a[i] <== left.prod[i] + c[i];
            carry.b[i] <== right.prod[i] + prod[i];
        } else {
            carry.a[i] <== left.prod[i];
            carry.b[i] <== right.prod[i];
        }
    }
}

template RabinVerifier(w, n) {
    // w * n is enough bits to store `sig`.
    // Constraints:
    //   $2(2n - 1)$    for the two polynomial multipliers
    //   $nw$           to check the bits of x
    //   $(2n - 2)(w + 2 + ceil(log2(2n - 1))) + 1$ for the carried equality
    //   Net:
    //      2n(1.5w + ceil(log2(n)) + 5) - 2w - 7

    // Checks: sig * sig == x * pk + msg

    signal input sig[n];
    signal input msg[n];
    signal input pk[n];

    signal x[n];

    //Compute the x
    compute {
        int sigAcc = int(0);
        int msgAcc = int(0);
        int pkAcc = int(0);
        for (int i = int(0); i < int(n); i++) {
            sigAcc += int(sig[i]) << (int(w) * i);
            msgAcc += int(msg[i]) << (int(w) * i);
            pkAcc  += int(pk[i])  << (int(w) * i);
        }
        int xAcc = (sigAcc * sigAcc - msgAcc) / pkAcc;
        for (int i = int(0); i < int(n); i++) {
            x[i] <-- field(xAcc % int(2 ** w));
            xAcc = xAcc \ int(2 ** w);
        }
        xAcc === int(0);
    }

    // Verify the wordness of x lest our multipliers break
    component xBits[n];
    for (var i = 0; i < n; i++) {
        xBits[i] = Num2Bits(w);
        xBits[i].in <== x[i];
    }

    component left = PolynomialMultiplier(n);
    component right = PolynomialMultiplier(n);

    for (var i = 0; i < n; i++) {
        left.a[i] <== sig[i];
        left.b[i] <== sig[i];
        right.a[i] <== x[i];
        right.b[i] <== pk[i];
    }

    component equality = EqualWhenCarried(w, 2 * n - 1);

    for (var i = 0; i < 2 * n - 1; i++) {
        if (i < n) {
            equality.a[i] <== left.prod[i];
            equality.b[i] <== right.prod[i] + msg[i];
        } else {
            equality.a[i] <== left.prod[i];
            equality.b[i] <== right.prod[i];
        }
    }

}
