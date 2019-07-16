const chai = require("chai");
const path = require("path");
const snarkjs = require("snarkjs");

const compiler = require("circom");


const assert = chai.assert;
chai.should();

describe("WordMultiplier", () => {
    it("should be compilable", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_4.circom"));
        new snarkjs.Circuit(cirDef);
    });

    it("should have 4 + 4 + 1 constraints (4 bits/word)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_4.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.nConstraints.should.equal(4 + 4 + 1);
    });

    it("should compute 15 * 3 = 2,13 (4 bits/word)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_4.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a": "15",
            "b": "3",
            "prod": "13",
            "carry": "2",
        });
        assert(witness[circuit.signalName2Idx["main.prod"]].equals(snarkjs.bigInt(13)));
        assert(witness[circuit.signalName2Idx["main.carry"]].equals(snarkjs.bigInt(2)));
    });
});

describe("WordMultiplierWithCarry", () => {
    it("should be compilable", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_carry_4.circom"));
        new snarkjs.Circuit(cirDef);
    });

    it("should have 4 + 4 + 1 constraints (4 bits/word)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_carry_4.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.nConstraints.should.equal(4 + 4 + 1);
    });
    it("should compute 15 * 3 + 6 = 3,3 (4 bits/word)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_carry_4.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a": "15",
            "b": "3",
            "carryIn1": 6,
            "carryIn2": 0,
        });
        assert(witness[circuit.signalName2Idx["main.prod"]].equals(snarkjs.bigInt(3)));
        assert(witness[circuit.signalName2Idx["main.carryOut"]].equals(snarkjs.bigInt(3)));
    });
    it("should compute 15 * 15 + 15 + 15 = 15,15 (4 bits/word)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "word_multiplier_carry_4.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a": "15",
            "b": "15",
            "carryIn1": 15,
            "carryIn2": 15,
        });
        assert(witness[circuit.signalName2Idx["main.prod"]].equals(snarkjs.bigInt(15)));
        assert(witness[circuit.signalName2Idx["main.carryOut"]].equals(snarkjs.bigInt(15)));
    });
});

describe("NBy1Multiplier", () => {
    it("should be compilable", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "n_by_1_mult_4bit_2word.circom"));
        new snarkjs.Circuit(cirDef);
    });

    it("should have 18 constraints", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "n_by_1_mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.nConstraints.should.equal(18);
    });

    it("should compute 3,3 * 13 = 2,9,7 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "n_by_1_mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "3",
            "a[1]": "3",
            "b": "13",
            "c[0]" : "0",
            "c[1]" : "0",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(7)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(9)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(2)));
    });
    it("should compute 15,15 * 15 + 15,15 = 15,15,0 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "n_by_1_mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "15",
            "a[1]": "15",
            "b": "15",
            "c[0]" : "15",
            "c[1]" : "15",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(15)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(15)));
    });
});

describe("Multiplier", () => {
    it("should be compilable", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        new snarkjs.Circuit(cirDef);
    });

    it("should have 36 constraints", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.nConstraints.should.equal(36);
    });

    it("should compute 1 * 1 = 1 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "1",
            "a[1]": "0",
            "b[0]": "1",
            "b[1]": "0",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(1)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(0)));
    });

    it("should compute 1,0 * 1,0 = 1,0,0 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "0",
            "a[1]": "1",
            "b[0]": "0",
            "b[1]": "1",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(1)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(0)));
    });

    it("should compute 1,3 * 3,0 = 0,3,9,0 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "3",
            "a[1]": "1",
            "b[0]": "0",
            "b[1]": "3",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(9)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(3)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(0)));
    });

    it("should compute 3,0 * 1,3  = 0,3,9,0 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "0",
            "a[1]": "3",
            "b[0]": "3",
            "b[1]": "1",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(9)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(3)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(0)));
    });

    it("should compute 8,7 * 9,3  = 4,13,8,5 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "7",
            "a[1]": "8",
            "b[0]": "3",
            "b[1]": "9",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(5)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(8)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(13)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(4)));
    });

    it("should compute 9,3 * 8,7 = 4,13,8,5 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "3",
            "a[1]": "9",
            "b[0]": "7",
            "b[1]": "8",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(5)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(8)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(13)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(4)));
    });
    it("should compute 15,15 * 15,15 = 15,14,0,1 (4 bits/word, 2 words)", async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_4bit_2word.circom"));
        const circuit = new snarkjs.Circuit(cirDef);
        const witness = circuit.calculateWitness({
            "a[0]": "15",
            "a[1]": "15",
            "b[0]": "15",
            "b[1]": "15",
        });
        assert(witness[circuit.signalName2Idx["main.prod[0]"]].equals(snarkjs.bigInt(1)));
        assert(witness[circuit.signalName2Idx["main.prod[1]"]].equals(snarkjs.bigInt(0)));
        assert(witness[circuit.signalName2Idx["main.prod[2]"]].equals(snarkjs.bigInt(14)));
        assert(witness[circuit.signalName2Idx["main.prod[3]"]].equals(snarkjs.bigInt(15)));
    });
});
