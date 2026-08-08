/*

scramble_333.js

3x3x3 Solver / Scramble Generator in Javascript.

The core 3x3x3 code is from a min2phase solver by Shuang Chen.
Compiled to Javascript using GWT and j2js project.

new feature:
remove flip twist pruning table
reduce memory used
initialization time is decreased to about 40% (200ms / 500ms)
average solving time is increased to about 150% (10ms / 7ms)

 */
"use strict";

if (typeof scramblers == "undefined") {
	var scramblers = {};
}

scramblers["333fm"] = scramblers["333ft"] = scramblers["333bf"] = scramblers["333oh"] = scramblers["333"] = (function() {

"use strict";

function createArray(length1, length2){
	var result, i;
	result = [];
	if (length2 != undefined) {
		for (i=0; i<length1; i++) {
			result[i] = [];
		}	
	}
	return result;
}

function CoordCube_$clinit(){
	UDSliceMove = createArray(495, 18);
	TwistMove = createArray(324, 18);
	FlipMove =  createArray(336, 18);
	UDSliceConj =  createArray(495, 8);
	UDSliceTwistPrun = createArray(20048);
	UDSliceFlipPrun = createArray(20790);
	CPermMove =  createArray(2768, 18);
	EPermMove =  createArray(2768, 10);
	MPermMove =  createArray(24, 10);
	MPermConj =  createArray(24, 16);
	MCPermPrun = createArray(8304);
	MEPermPrun = createArray(8304);
}

function getPruning(table, index){
	return table[index >> 3] >> ((index & 7) << 2) & 15;
}

function initCPermMove(){
	var c, d, i, j;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 2768; ++i) {
		$setCPerm(c, epermS2R[i]);
		for (j = 0; j < 18; ++j) {
			cornMult(c, moveCube[j], d);
			CPermMove[i][j] = $getCPermSym(d);
		}
	}
}

function initEPermMove(){
	var c, d, i, j;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 2768; ++i) {
		$setEPerm(c, epermS2R[i]);
		for (j = 0; j < 10; ++j) {
			EdgeMult(c, moveCube[ud2std[j]], d);
			EPermMove[i][j] = $getEPermSym(d);
		}
	}
}

function initFlipMove(){
	var c, d, i, j;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 336; ++i) {
		$setFlip(c, FlipS2R[i]);
		for (j = 0; j < 18; ++j) {
			EdgeMult(c, moveCube[j], d);
			FlipMove[i][j] = $getFlipSym(d);
		}
	}
}

function initMPermMoveConj(){
	var c, d, i, j;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 24; ++i) {
		setComb(c.ep, i << 9);
		for (j = 0; j < 10; ++j) {
			EdgeMult(c, moveCube[ud2std[j]], d);
			MPermMove[i][j] = getComb(d.ep, 8) >> 9;
		}
		for (j = 0; j < 16; ++j) {
			EdgeConjugate(c, SymInv[j], d);
			MPermConj[i][j] = getComb(d.ep, 8) >> 9;
		}
	}
}

function initRawSymPrun(PrunTable, INV_DEPTH, RawMove, RawConj, SymMove, SymState, SymSwitch, moveMap, SYM_SHIFT){
	var N_MOVES, N_RAW, N_SIZE, N_SYM, SYM_MASK, check, depth, done, end, i, idx, idxx, inv, j, m, raw, rawx, select, sym, symState, symx, val, fill, len;
	SYM_MASK = (1 << SYM_SHIFT) - 1;
	N_RAW = RawMove.length;
	N_SYM = SymMove.length;
	N_SIZE = N_RAW * N_SYM;
	N_MOVES = RawMove[0].length;
	for (i = 0, len = (N_RAW * N_SYM + 7) >> 3; i < len; ++i) {
		PrunTable[i] = -1;
	}
	PrunTable[0] ^= 15;
	depth = 0;
	done = 1;
	while (done < N_SIZE) {
		inv = depth > INV_DEPTH;
		select = inv?15:depth;
		check = inv?depth:15;
		++depth;
		fill = depth ^ 15;
		for (i = 0; i < N_SIZE;) {
			val = PrunTable[i >> 3];
			if (!inv && val == -1) {
				i += 8;
				continue;
			}
			for (end = i + 8 < N_SIZE?i + 8:N_SIZE; i < end; ++i , val >>= 4) {
				if ((val & 15) == select) {
					raw = i % N_RAW;
					sym = ~~(i / N_RAW);
					for (m = 0; m < N_MOVES; ++m) {
						symx = SymMove[sym][moveMap == null?m:moveMap[m]];
						rawx = RawConj[RawMove[raw][m] & 511][symx & SYM_MASK];
						symx >>>= SYM_SHIFT;
						idx = symx * N_RAW + rawx;
						if ((PrunTable[idx >> 3] >> ((idx & 7) << 2) & 15) == check) {
							++done;
							if (inv) {
								PrunTable[i >> 3] ^= fill << ((i & 7) << 2);
								break;
							}
							 else {
								PrunTable[idx >> 3] ^= fill << ((idx & 7) << 2);
								for (j = 1 , symState = SymState[symx]; (symState >>= 1) != 0; ++j) {
									if ((symState & 1) == 1) {
										idxx = symx * N_RAW + RawConj[rawx][j ^ (SymSwitch == null?0:SymSwitch[j])];
										if ((PrunTable[idxx >> 3] >> ((idxx & 7) << 2) & 15) == 15) {
											PrunTable[idxx >> 3] ^= fill << ((idxx & 7) << 2);
											++done;
										}
									}
								}
							}
						}
					}
				}
			}
		}
//		console.log(done);
	}
}

function initTwistMove(){
	var c, d, i, j;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 324; ++i) {
		$setTwist(c, TwistS2R[i]);
		for (j = 0; j < 18; ++j) {
			cornMult(c, moveCube[j], d);
			TwistMove[i][j] = $getTwistSym(d);
		}
	}
}

function initUDSliceMoveConj(){
	var c, cx, d, i, j, k, udslice;
	c = new CubieCube;
	d = new CubieCube;
	for (i = 0; i < 495; ++i) {
		setComb(c.ep, i);
		for (j = 0; j < 18; j += 3) {
			EdgeMult(c, moveCube[j], d);
			UDSliceMove[i][j] = getComb(d.ep, 8);
		}
		for (j = 0; j < 16; j += 2) {
			EdgeConjugate(c, SymInv[j], d);
			UDSliceConj[i][j >>> 1] = getComb(d.ep, 8) & 511;
		}
	}
	for (i = 0; i < 495; ++i) {
		for (j = 0; j < 18; j += 3) {
			udslice = UDSliceMove[i][j];
			for (k = 1; k < 3; ++k) {
				cx = UDSliceMove[udslice & 511][j];
				udslice = permMult[udslice >>> 9][cx >>> 9] << 9 | cx & 511;
				UDSliceMove[i][j + k] = udslice;
			}
		}
	}
}

var CPermMove, EPermMove, FlipMove, MCPermPrun, MEPermPrun, MPermConj, MPermMove, TwistMove, UDSliceConj, UDSliceFlipPrun, UDSliceMove, UDSliceTwistPrun;
function CubieCube_$clinit(){
	CubeSym = createArray(16);
	moveCube = createArray(18);
	SymInv = createArray(16, 1);
	SymMult = createArray(16, 16);
	SymMove = createArray(16, 18);
	Sym8Mult = createArray(8, 8);
	Sym8Move = createArray(8, 18);
	Sym8MultInv = createArray(8, 8);
	SymMoveUD = createArray(16, 10);
	FlipS2R = createArray(336);
	TwistS2R = createArray(324);
	epermS2R = createArray(2768);
	e2c = [0, 0, 0, 0, 1, 3, 1, 3, 1, 3, 1, 3, 0, 0, 0, 0];
	MtoEPerm = createArray(40320);
	SymStateTwist = createArray(324);
	SymStateFlip = createArray(336);
	SymStatePerm = createArray(2768);
	urf1 = new CubieCube1(2531, 1373, 67026819, 1367);
	urf2 = new CubieCube1(2089, 1906, 322752913, 2040);
	urfMove = [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], [6, 7, 8, 0, 1, 2, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 14], [3, 4, 5, 6, 7, 8, 0, 1, 2, 12, 13, 14, 15, 16, 17, 9, 10, 11], [2, 1, 0, 5, 4, 3, 8, 7, 6, 11, 10, 9, 14, 13, 12, 17, 16, 15], [8, 7, 6, 2, 1, 0, 5, 4, 3, 17, 16, 15, 11, 10, 9, 14, 13, 12], [5, 4, 3, 8, 7, 6, 2, 1, 0, 14, 13, 12, 17, 16, 15, 11, 10, 9]];
}

function CubieCube_$$init(obj){
	obj.cp = [0, 1, 2, 3, 4, 5, 6, 7];
	obj.co = [0, 0, 0, 0, 0, 0, 0, 0];
	obj.ep = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
	obj.eo = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
}

function $copy(obj, c){
	var i;
	for (i = 0; i < 8; ++i) {
		obj.cp[i] = c.cp[i];
		obj.co[i] = c.co[i];
	}
	for (i = 0; i < 12; ++i) {
		obj.ep[i] = c.ep[i];
		obj.eo[i] = c.eo[i];
	}
}

function $getCPermSym(obj){
	var idx;
	idx = epermR2S[get8Perm(obj.cp)];
	idx ^= e2c[idx & 15];
	return idx;
}

function $getEPermSym(obj){
	return epermR2S[get8Perm(obj.ep)];
}

function $getFlip(obj){
	var i, idx;
	idx = 0;
	for (i = 0; i < 11; ++i) {
		idx <<= 1;
		idx |= obj.eo[i];
	}
	return idx;
}

function $getFlipSym(obj){
	return FlipR2S[$getFlip(obj)];
}

function $getTwist(obj){
	var i, idx;
	idx = 0;
	for (i = 0; i < 7; ++i) {
		idx *= 3;
		idx += obj.co[i];
	}
	return idx;
}

function $getTwistSym(obj){
	return TwistR2S[$getTwist(obj)];
}

function $invCubieCube(obj){
	var corn, edge, ori;
	for (edge = 0; edge < 12; ++edge)
		obj.temps.ep[obj.ep[edge]] = edge;
	for (edge = 0; edge < 12; ++edge)
		obj.temps.eo[edge] = obj.eo[obj.temps.ep[edge]];
	for (corn = 0; corn < 8; ++corn)
		obj.temps.cp[obj.cp[corn]] = corn;
	for (corn = 0; corn < 8; ++corn) {
		ori = obj.co[obj.temps.cp[corn]];
		obj.temps.co[corn] = -ori;
		obj.temps.co[corn] < 0 && (obj.temps.co[corn] = obj.temps.co[corn] + 3);
	}
	$copy(obj, obj.temps);
}

function $setCPerm(obj, idx){
	set8Perm(obj.cp, idx);
}

function $setEPerm(obj, idx){
	set8Perm(obj.ep, idx);
}

function $setFlip(obj, idx){
	var i, parity;
	parity = 0;
	for (i = 10; i >= 0; --i) {
		parity ^= obj.eo[i] = (idx & 1);
		idx >>= 1;
	}
	obj.eo[11] = parity;
}

function $setTwist(obj, idx){
	var i, twst;
	twst = 0;
	for (i = 6; i >= 0; --i) {
		twst += obj.co[i] = idx % 3;
		idx = ~~(idx / 3);
	}
	obj.co[7] = (15 - twst) % 3;
}

function $verify(obj){
	var c, cornMask, e, edgeMask, i, sum;
	sum = 0;
	edgeMask = 0;
	for (e = 0; e < 12; ++e)
		edgeMask |= 1 << obj.ep[e];
	if (edgeMask != 4095)
		return -2;
	for (i = 0; i < 12; ++i)
		sum ^= obj.eo[i];
	if (sum % 2 != 0)
		return -3;
	cornMask = 0;
	for (c = 0; c < 8; ++c)
		cornMask |= 1 << obj.cp[c];
	if (cornMask != 255)
		return -4;
	sum = 0;
	for (i = 0; i < 8; ++i)
		sum += obj.co[i];
	if (sum % 3 != 0)
		return -5;
	if ((getNParity(getNPerm(obj.ep, 12), 12) ^ getNParity(get8Perm(obj.cp), 8)) != 0)
		return -6;
	return 0;
}

function cornConjugate(a, idx, b){
	var corn, oriA, oriB, s, sinv;
	sinv = CubeSym[SymInv[idx]];
	s = CubeSym[idx];
	for (corn = 0; corn < 8; ++corn) {
		b.cp[corn] = sinv.cp[a.cp[s.cp[corn]]];
		oriA = sinv.co[a.cp[s.cp[corn]]];
		oriB = a.co[s.cp[corn]];
		b.co[corn] = oriA < 3?oriB:(3 - oriB) % 3;
	}
}

function cornMult(a, b, prod){
	var corn, ori, oriA, oriB;
	for (corn = 0; corn < 8; ++corn) {
		prod.cp[corn] = a.cp[b.cp[corn]];
		oriA = a.co[b.cp[corn]];
		oriB = b.co[corn];
		ori = oriA;
		ori += oriA < 3?oriB:6 - oriB;
		ori %= 3;
		oriA >= 3 ^ oriB >= 3 && (ori += 3);
		prod.co[corn] = ori;
	}
}

function CubieCube(){
	CubieCube_$$init(this);
}

function CubieCube1(cperm, twist, eperm, flip){
	CubieCube_$$init(this);
	set8Perm(this.cp, cperm);
	$setTwist(this, twist);
	setNPerm(this.ep, eperm, 12);
	$setFlip(this, flip);
}

function CubieCube2(c){
	CubieCube_$$init(this);
	$copy(this, c);
}

function EdgeConjugate(a, idx, b){
	var ed, s, sinv;
	sinv = CubeSym[SymInv[idx]];
	s = CubeSym[idx];
	for (ed = 0; ed < 12; ++ed) {
		b.ep[ed] = sinv.ep[a.ep[s.ep[ed]]];
		b.eo[ed] = s.eo[ed] ^ a.eo[s.ep[ed]] ^ sinv.eo[a.ep[s.ep[ed]]];
	}
}

function EdgeMult(a, b, prod){
	var ed;
	for (ed = 0; ed < 12; ++ed) {
		prod.ep[ed] = a.ep[b.ep[ed]];
		prod.eo[ed] = b.eo[ed] ^ a.eo[b.ep[ed]];
	}
}

function initFlipSym2Raw(){
	var c, count, d, i, idx, occ, s;
	c = new CubieCube;
	d = new CubieCube;
	occ = createArray(64);
	count = 0;
	for (i = 0; i < 64; occ[i++] = 0) {}
	FlipR2S = createArray(2048);
	for (i = 0; i < 2048; ++i) {
		if ((occ[i >> 5] & 1 << (i & 31)) == 0) {
			$setFlip(c, i);
			for (s = 0; s < 16; s += 2) {
				EdgeConjugate(c, s, d);
				idx = $getFlip(d);
				idx == i && (SymStateFlip[count] |= 1 << (s >> 1));
				occ[idx >> 5] |= 1 << (idx & 31);
				FlipR2S[idx] = count << 3 | s >> 1;
			}
			FlipS2R[count++] = i;
		}
	}
}

function initMove(){
	var a, p;
	moveCube[0] = new CubieCube1(15120, 0, 119750400, 0);
	moveCube[3] = new CubieCube1(21021, 1494, 323403417, 0);
	moveCube[6] = new CubieCube1(8064, 1236, 29441808, 550);
	moveCube[9] = new CubieCube1(9, 0, 5880, 0);
	moveCube[12] = new CubieCube1(1230, 412, 2949660, 0);
	moveCube[15] = new CubieCube1(224, 137, 328552, 137);
	for (a = 0; a < 18; a += 3) {
		for (p = 0; p < 2; ++p) {
			moveCube[a + p + 1] = new CubieCube;
			EdgeMult(moveCube[a + p], moveCube[a], moveCube[a + p + 1]);
			cornMult(moveCube[a + p], moveCube[a], moveCube[a + p + 1]);
		}
	}
}

function initPermSym2Raw(){
	var a, b, c, count, d, i, idx, m, occ, s;
	c = new CubieCube;
	d = new CubieCube;
	occ = createArray(1260);
	count = 0;
	for (i = 0; i < 1260; occ[i++] = 0) {}
	epermR2S = createArray(40320);
	for (i = 0; i < 40320; ++i) {
		if ((occ[i >> 5] & 1 << (i & 31)) == 0) {
			set8Perm(c.ep, i);
			for (s = 0; s < 16; ++s) {
				EdgeConjugate(c, s, d);
				idx = get8Perm(d.ep);
				idx == i && (SymStatePerm[count] |= 1 << s);
				occ[idx >> 5] |= 1 << (idx & 31);
				a = getComb(d.ep, 0);
				b = getComb(d.ep, 4) >> 9;
				m = 494 - (a & 511) + (a >> 9) * 70 + b * 1680;
				MtoEPerm[m] = epermR2S[idx] = count << 4 | s;
			}
			epermS2R[count++] = i;
		}
	}
}

function initSym(){
	var c, d, f2, i, j, k, lr2, m, s, t, u4;
	c = new CubieCube;
	d = new CubieCube;
	f2 = new CubieCube1(28783, 0, 259268407, 0);
	u4 = new CubieCube1(15138, 0, 119765538, 7);
	lr2 = new CubieCube1(5167, 0, 83473207, 0);
	lr2.co = [3, 3, 3, 3, 3, 3, 3, 3];
	for (i = 0; i < 16; ++i) {
		CubeSym[i] = new CubieCube2(c);
		cornMult(c, u4, d);
		EdgeMult(c, u4, d);
		t = d;
		d = c;
		c = t;
		if (i % 4 == 3) {
			cornMult(t, lr2, d);
			EdgeMult(t, lr2, d);
			t = d;
			d = c;
			c = t;
		}
		if (i % 8 == 7) {
			cornMult(t, f2, d);
			EdgeMult(t, f2, d);
			t = d;
			d = c;
			c = t;
		}
	}
	for (i = 0; i < 16; ++i) {
		for (j = 0; j < 16; ++j) {
			cornMult(CubeSym[i], CubeSym[j], c);
			for (k = 0; k < 16; ++k) {
				if (CubeSym[k].cp[0] == c.cp[0] && CubeSym[k].cp[1] == c.cp[1] && CubeSym[k].cp[2] == c.cp[2]) {
					SymMult[i][j] = k;
					k == 0 && (SymInv[i] = j);
					break;
				}
			}
		}
	}
	for (j = 0; j < 18; ++j) {
		for (s = 0; s < 16; ++s) {
			cornConjugate(moveCube[j], SymInv[s], c);
			CONTINUE: for (m = 0; m < 18; ++m) {
				for (i = 0; i < 8; i += 2) {
					if (c.cp[i] != moveCube[m].cp[i]) {
						continue CONTINUE;
					}
				}
				SymMove[s][j] = m;
				break;
			}
		}
	}
	for (j = 0; j < 10; ++j) {
		for (s = 0; s < 16; ++s) {
			SymMoveUD[s][j] = std2ud[SymMove[s][ud2std[j]]];
		}
	}
	for (j = 0; j < 8; ++j) {
		for (s = 0; s < 8; ++s) {
			Sym8Mult[j][s] = SymMult[j << 1][s << 1] >> 1;
			Sym8MultInv[j][s] = SymMult[j << 1][SymInv[s << 1]] >> 1;
		}
	}
	for (j = 0; j < 18; ++j) {
		for (s = 0; s < 8; ++s) {
			Sym8Move[s][j] = SymMove[s << 1][j];
		}
	}
}

function initTwistSym2Raw(){
	var c, count, d, i, idx, occ, s;
	c = new CubieCube;
	d = new CubieCube;
	occ = createArray(69);
	count = 0;
	for (i = 0; i < 69; occ[i++] = 0) {}
	TwistR2S = createArray(2187);
	for (i = 0; i < 2187; ++i) {
		if ((occ[i >> 5] & 1 << (i & 31)) == 0) {
			$setTwist(c, i);
			for (s = 0; s < 16; s += 2) {
				cornConjugate(c, s, d);
				idx = $getTwist(d);
				idx == i && (SymStateTwist[count] = (SymStateTwist[count] | 1 << (s >> 1)));
				occ[idx >> 5] |= 1 << (idx & 31);
				TwistR2S[idx] = (count << 3 | s >> 1);
			}
			TwistS2R[count++] = i;
		}
	}
}
 
var _ = CubieCube2.prototype = CubieCube1.prototype = CubieCube.prototype;
_.temps = null;
var CubeSym, epermR2S = null, epermS2R, FlipR2S = null, FlipS2R, MtoEPerm, Sym8Move, Sym8Mult, Sym8MultInv, SymInv, SymMove, SymMoveUD, SymMult, SymStateFlip, SymStatePerm, SymStateTwist, TwistR2S = null, TwistS2R, e2c, moveCube, urf1, urf2, urfMove;
function $initPhase2(obj){
	var cidx, csym, cx, d4e, depth2, edge, esym, i, lm, m, mid, prun, u4e;
	if (+new Date > (obj.solution == null?obj.timeOut:obj.timeMin)) {
		return 0;
	}
	obj.valid2 = Math.min(obj.valid2, obj.valid1);
	cidx = obj.corn[obj.valid1] >>> 4;
	csym = obj.corn[obj.valid1] & 15;
	for (i = obj.valid1; i < obj.depth1; ++i) {
		m = obj.move[i];
		cidx = CPermMove[cidx][SymMove[csym][m]];
		csym = SymMult[cidx & 15][csym];
		cidx >>>= 4;
		obj.corn[i + 1] = cidx << 4 | csym;
		cx = UDSliceMove[obj.mid4[i] & 511][m];
		obj.mid4[i + 1] = permMult[obj.mid4[i] >>> 9][cx >>> 9] << 9 | cx & 511;
	}
	obj.valid1 = obj.depth1;
	mid = obj.mid4[obj.depth1] >>> 9;
	prun = getPruning(MCPermPrun, cidx * 24 + MPermConj[mid][csym]);
	if (prun >= obj.maxDep2) {
		return prun > obj.maxDep2?2:1;
	}
	u4e = obj.ud8e[obj.valid2] >>> 16;
	d4e = obj.ud8e[obj.valid2] & 65535;
	for (i = obj.valid2; i < obj.depth1; ++i) {
		m = obj.move[i];
		cx = UDSliceMove[u4e & 511][m];
		u4e = permMult[u4e >>> 9][cx >>> 9] << 9 | cx & 511;
		cx = UDSliceMove[d4e & 511][m];
		d4e = permMult[d4e >>> 9][cx >>> 9] << 9 | cx & 511;
		obj.ud8e[i + 1] = u4e << 16 | d4e;
	}
	obj.valid2 = obj.depth1;
	edge = MtoEPerm[494 - (u4e & 511) + (u4e >>> 9) * 70 + (d4e >>> 9) * 1680];
	esym = edge & 15;
	edge >>>= 4;
	prun = Math.max(getPruning(MEPermPrun, edge * 24 + MPermConj[mid][esym]), prun);
	if (prun >= obj.maxDep2) {
		return prun > obj.maxDep2?2:1;
	}
	lm = obj.depth1 == 0?10:std2ud[~~(obj.move[obj.depth1 - 1] / 3) * 3 + 1];
	for (depth2 = prun; depth2 < obj.maxDep2; ++depth2) {
		if ($phase2(obj, edge, esym, cidx, csym, mid, depth2, obj.depth1, lm)) {
			obj.sol = obj.depth1 + depth2;
			obj.maxDep2 = Math.min(12, obj.sol - obj.depth1);
			obj.solution = $solutionToString(obj);
			return (+new Date > obj.timeMin)?0:1;
		}
	}
	return 1;
}

function $phase1(obj, twist, tsym, flip, fsym, slice, maxl, lm){
	var axis, flipx, fsymx, m, power, prun, ret, slicex, tsymx, twistx;
	if (twist == 0 && flip == 0 && slice == 0 && maxl < 5) {
		return maxl == 0?$initPhase2(obj):1;
	}
	for (axis = 0; axis < 18; axis += 3) {
		if (axis == lm || axis == lm - 9) {
			continue;
		}
		for (power = 0; power < 3; ++power) {
			m = axis + power;
			slicex = UDSliceMove[slice][m] & 511;
			twistx = TwistMove[twist][Sym8Move[tsym][m]];
			tsymx = Sym8Mult[twistx & 7][tsym];
			twistx >>>= 3;
			prun = getPruning(UDSliceTwistPrun, twistx * 495 + UDSliceConj[slicex][tsymx]);
			if (prun > maxl) {
				break;
			}
			 else if (prun == maxl) {
				continue;
			}
			flipx = FlipMove[flip][Sym8Move[fsym][m]];
			fsymx = Sym8Mult[flipx & 7][fsym];
			flipx >>>= 3;
			prun = getPruning(UDSliceFlipPrun, flipx * 495 + UDSliceConj[slicex][fsymx]);
			if (prun > maxl) {
				break;
			}
			 else if (prun == maxl) {
				continue;
			}
			obj.move[obj.depth1 - maxl] = m;
			obj.valid1 = Math.min(obj.valid1, obj.depth1 - maxl);
			ret = $phase1(obj, twistx, tsymx, flipx, fsymx, slicex, maxl - 1, axis);
			if (ret != 1) {
				return ret >> 1;
			}
		}
	}
	return 1;
}

function $phase2(obj, eidx, esym, cidx, csym, mid, maxl, depth, lm){
	var cidxx, csymx, eidxx, esymx, m, midx;
	if (eidx == 0 && cidx == 0 && mid == 0) {
		return true;
	}
	for (m = 0; m < 10; ++m) {
		if (ckmv2[lm][m]) {
			continue;
		}
		midx = MPermMove[mid][m];
		cidxx = CPermMove[cidx][SymMove[csym][ud2std[m]]];
		csymx = SymMult[cidxx & 15][csym];
		cidxx >>>= 4;
		if (getPruning(MCPermPrun, cidxx * 24 + MPermConj[midx][csymx]) >= maxl) {
			continue;
		}
		eidxx = EPermMove[eidx][SymMoveUD[esym][m]];
		esymx = SymMult[eidxx & 15][esym];
		eidxx >>>= 4;
		if (getPruning(MEPermPrun, eidxx * 24 + MPermConj[midx][esymx]) >= maxl) {
			continue;
		}
		if ($phase2(obj, eidxx, esymx, cidxx, csymx, midx, maxl - 1, depth + 1, m)) {
			obj.move[depth] = ud2std[m];
			return true;
		}
	}
	return false;
}

function $solution(obj, facelets, maxDepth, timeOut, timeMin, verbose){
	var check;
	check = Search_$verify(obj, facelets);
	if (check != 0) {
		return 'Error ' + (check < 0?-check:check);
	}
	obj.sol = (maxDepth || 21) + 1;
	obj.timeOut = +new Date + (timeOut || 1000);
	obj.timeMin = obj.timeOut + Math.min((timeMin || 50) - (timeOut || 1000), 0);
	obj.verbose = verbose || 2;
	obj.solution = null;
	return $solve(obj, obj.cc);
}

function $solutionToString(obj){
	var s, sb, urf;
	sb = '';
	urf = (obj.verbose & 2) != 0?(obj.urfIdx + 3) % 6:obj.urfIdx;
	if (urf < 3) {
		for (s = 0; s < obj.depth1; ++s) {
			sb += move2str[urfMove[urf][obj.move[s]]] + ' ';
		}
		(obj.verbose & 1) != 0 && (sb += '.  ');
		for (s = obj.depth1; s < obj.sol; ++s) {
			sb += move2str[urfMove[urf][obj.move[s]]] + ' ';
		}
	}
	 else {
		for (s = obj.sol - 1; s >= obj.depth1; --s) {
			sb += move2str[urfMove[urf][obj.move[s]]] + ' ';
		}
		(obj.verbose & 1) != 0 && (sb += '.  ');
		for (s = obj.depth1 - 1; s >= 0; --s) {
			sb += move2str[urfMove[urf][obj.move[s]]] + ' ';
		}
	}
	(obj.verbose & 4) != 0 && (sb += '(' + obj.sol + 'f)');
	return sb;
}

function $solve(obj, c){
	var conjMask, i, j;
	conjMask = 0;
	for (i = 0; i < 6; ++i) {
		obj.twist[i] = $getTwistSym(c);
		obj.flip[i] = $getFlipSym(c);
		obj.slice[i] = getComb(c.ep, 8);
		obj.corn0[i] = $getCPermSym(c);
		obj.ud8e0[i] = getComb(c.ep, 0) << 16 | getComb(c.ep, 4);
		for (j = 0; j < i; ++j) {
			if (obj.twist[i] == obj.twist[j] && obj.flip[i] == obj.flip[j] && obj.slice[i] == obj.slice[j] && obj.corn0[i] == obj.corn0[j] && obj.ud8e0[i] == obj.ud8e0[j]) {
				conjMask |= 1 << i;
				break;
			}
		}
		(conjMask & 1 << i) == 0 && (obj.prun[i] = Math.max(Math.max(getPruning(UDSliceTwistPrun, (obj.twist[i] >>> 3) * 495 + UDSliceConj[obj.slice[i] & 511][obj.twist[i] & 7]), getPruning(UDSliceFlipPrun, (obj.flip[i] >>> 3) * 495 + UDSliceConj[obj.slice[i] & 511][obj.flip[i] & 7])), 0));
		!c.temps && (c.temps = new CubieCube);
		cornMult(urf2, c, c.temps);
		cornMult(c.temps, urf1, c);
		EdgeMult(urf2, c, c.temps);
		EdgeMult(c.temps, urf1, c);
		i == 2 && $invCubieCube(c);
	}
	for (obj.depth1 = 0; obj.depth1 < obj.sol; ++obj.depth1) {
		obj.maxDep2 = Math.min(12, obj.sol - obj.depth1);
		for (obj.urfIdx = 0; obj.urfIdx < 6; ++obj.urfIdx) {
			if ((conjMask & 1 << obj.urfIdx) != 0) {
				continue;
			}
			obj.corn[0] = obj.corn0[obj.urfIdx];
			obj.mid4[0] = obj.slice[obj.urfIdx];
			obj.ud8e[0] = obj.ud8e0[obj.urfIdx];
			if (obj.prun[obj.urfIdx] <= obj.depth1 && $phase1(obj, obj.twist[obj.urfIdx] >>> 3, obj.twist[obj.urfIdx] & 7, obj.flip[obj.urfIdx] >>> 3, obj.flip[obj.urfIdx] & 7, obj.slice[obj.urfIdx] & 511, obj.depth1, -1) == 0) {
				return obj.solution == null?'Error 8':obj.solution;
			}
		}
	}
	return obj.solution == null?'Error 7':obj.solution;
}

function Search_$verify(obj, facelets){
	var $e0, count, i;
	count = 0;
	for (i = 0; i < 54; ++i) {
		switch (facelets.charCodeAt(i)) {
			case 85:
				obj.f[i] = 0;
				break;
			case 82:
				obj.f[i] = 1;
				break;
			case 70:
				obj.f[i] = 2;
				break;
			case 68:
				obj.f[i] = 3;
				break;
			case 76:
				obj.f[i] = 4;
				break;
			case 66:
				obj.f[i] = 5;
				break;
			default:return -1;
		}
		count += 1 << (obj.f[i] << 2);
	}
	if (count != 10066329) {
		return -1;
	}
	toCubieCube(obj.f, obj.cc);
	return $verify(obj.cc);
}

function Search(){
	this.move = [];
	this.corn = [];
	this.mid4 = [];
	this.ud8e = [];
	this.twist = [];
	this.flip = [];
	this.slice = [];
	this.corn0 = [];
	this.ud8e0 = [];
	this.prun = [];
	this.f = [];
	this.cc = new CubieCube;
}

_ = Search.prototype;
_.depth1 = 0;
_.maxDep2 = 0;
_.sol = 0;
_.solution = null;
_.timeMin = 0;
_.timeOut = 0;
_.urfIdx = 0;
_.valid1 = 0;
_.valid2 = 0;
_.verbose = 0;

function Util_$clinit(){
	var arr1, arr2, arr3, i, ix, j, jx, k;
	cornerFacelet = [[8, 9, 20], [6, 18, 38], [0, 36, 47], [2, 45, 11], [29, 26, 15], [27, 44, 24], [33, 53, 42], [35, 17, 51]];
	edgeFacelet = [[5, 10], [7, 19], [3, 37], [1, 46], [32, 16], [28, 25], [30, 43], [34, 52], [23, 12], [21, 41], [50, 39], [48, 14]];
	Cnk = createArray(12, 12);
	fact = createArray(13);
	permMult = createArray(24, 24); 
	move2str = ['U ', 'U2', "U'", 'R ', 'R2', "R'", 'F ', 'F2', "F'", 'D ', 'D2', "D'", 'L ', 'L2', "L'", 'B ', 'B2', "B'"]; 
	ud2std = [0, 1, 2, 4, 7, 9, 10, 11, 13, 16];
	std2ud = createArray(18);
	ckmv2 = createArray(11, 10);
	for (i = 0; i < 10; ++i) {
		std2ud[ud2std[i]] = i;
	}
	for (i = 0; i < 10; ++i) {
		for (j = 0; j < 10; ++j) {
			ix = ud2std[i];
			jx = ud2std[j];
			ckmv2[i][j] = ~~(ix / 3) == ~~(jx / 3) || ~~(ix / 3) % 3 == ~~(jx / 3) % 3 && ix >= jx;
		}
		ckmv2[10][i] = false;
	}
	fact[0] = 1;
	for (i=0; i<12; ++i)
		for (j=0; j<12; ++j)
			Cnk[i][j] = 0;
	for (i = 0; i < 12; ++i) {
		Cnk[i][0] = Cnk[i][i] = 1;
		fact[i + 1] = fact[i] * (i + 1);
		for (j = 1; j < i; ++j) {
			Cnk[i][j] = Cnk[i - 1][j - 1] + Cnk[i - 1][j];
		}
	}
	arr1 = createArray(4);
	arr2 = createArray(4);
	arr3 = createArray(4);
	for (i = 0; i < 24; ++i) {
		for (j = 0; j < 24; ++j) {
			setNPerm(arr1, i, 4);
			setNPerm(arr2, j, 4);
			for (k = 0; k < 4; ++k) {
				arr3[k] = arr1[arr2[k]];
			}
			permMult[i][j] = getNPerm(arr3, 4);
		}
	}
}

function binarySearch(arr, key){
	var l, length, mid, r, val;
	length = arr.length;
	if (key <= arr[length - 1]) {
		l = 0;
		r = length - 1;
		while (l <= r) {
			mid = (l + r) >>> 1;
			val = arr[mid];
			if (key > val) {
				l = mid + 1;
			}
			 else if (key < val) {
				r = mid - 1;
			}
			 else {
				return mid;
			}
		}
	}
	return 65535;
}

function get8Perm(arr){
	var i, idx, v, val;
	idx = 0;
	val = 1985229328;
	for (i = 0; i < 7; ++i) {
		v = arr[i] << 2;
		idx = (8 - i) * idx + (val >> v & 7);
		val -= 286331152 << v;
	}
	return idx;
}

function getComb(arr, mask){
	var i, idxC, idxP, r, v, val;
	idxC = 0;
	idxP = 0;
	r = 4;
	val = 291;
	for (i = 11; i >= 0; --i) {
		if ((arr[i] & 12) == mask) {
			v = (arr[i] & 3) << 2;
			idxP = r * idxP + (val >> v & 15);
			val -= 273 >> 12 - v;
			idxC += Cnk[i][r--];
		}
	}
	return idxP << 9 | 494 - idxC;
}

function getNParity(idx, n){
	var i, p;
	p = 0;
	for (i = n - 2; i >= 0; --i) {
		p ^= idx % (n - i);
		idx = ~~(idx / (n - i));
	}
	return p & 1;
}

function getNPerm(arr, n){
	var i, idx, j;
	idx = 0;
	for (i = 0; i < n; ++i) {
		idx *= n - i;
		for (j = i + 1; j < n; ++j) {
			arr[j] < arr[i] && ++idx;
		}
	}
	return idx;
}

function set8Perm(arr, idx){
	var i, m, p, v, val;
	val = 1985229328;
	for (i = 0; i < 7; ++i) {
		p = fact[7 - i];
		v = ~~(idx / p);
		idx -= v * p;
		v <<= 2;
		arr[i] = val >> v & 7;
		m = (1 << v) - 1;
		val = (val & m) + (val >> 4 & ~m);
	}
	arr[7] = val;
}

function setComb(arr, idx){
	var fill, i, idxC, idxP, m, p, r, v, val;
	r = 4;
	fill = 11;
	val = 291;
	idxC = 494 - (idx & 511);
	idxP = idx >>> 9;
	for (i = 11; i >= 0; --i) {
		if (idxC >= Cnk[i][r]) {
			idxC -= Cnk[i][r--];
			p = fact[r & 3];
			v = ~~(idxP / p) << 2;
			idxP %= p;
			arr[i] = val >> v & 3 | 8;
			m = (1 << v) - 1;
			val = (val & m) + (val >> 4 & ~m);
		}
		 else {
			(fill & 12) == 8 && (fill -= 4);
			arr[i] = fill--;
		}
	}
}

function setNPerm(arr, idx, n){
	var i, j;
	arr[n - 1] = 0;
	for (i = n - 2; i >= 0; --i) {
		arr[i] = idx % (n - i);
		idx = ~~(idx / (n - i));
		for (j = i + 1; j < n; ++j) {
			arr[j] >= arr[i] && ++arr[j];
		}
	}
}

function toCubieCube(f, ccRet){
	var col1, col2, i, j, ori;
	for (i = 0; i < 8; ++i)
		ccRet.cp[i] = 0;
	for (i = 0; i < 12; ++i)
		ccRet.ep[i] = 0;
	for (i = 0; i < 8; ++i) {
		for (ori = 0; ori < 3; ++ori)
			if (f[cornerFacelet[i][ori]] == 0 || f[cornerFacelet[i][ori]] == 3)
				break;
		col1 = f[cornerFacelet[i][(ori + 1) % 3]];
		col2 = f[cornerFacelet[i][(ori + 2) % 3]];
		for (j = 0; j < 8; ++j) {
			if (col1 == ~~(cornerFacelet[j][1] / 9) && col2 == ~~(cornerFacelet[j][2] / 9)) {
				ccRet.cp[i] = j;
				ccRet.co[i] = ori % 3;
				break;
			}
		}
	}
	for (i = 0; i < 12; ++i) {
		for (j = 0; j < 12; ++j) {
			if (f[edgeFacelet[i][0]] == ~~(edgeFacelet[j][0] / 9) && f[edgeFacelet[i][1]] == ~~(edgeFacelet[j][1] / 9)) {
				ccRet.ep[i] = j;
				ccRet.eo[i] = 0;
				break;
			}
			if (f[edgeFacelet[i][0]] == ~~(edgeFacelet[j][1] / 9) && f[edgeFacelet[i][1]] == ~~(edgeFacelet[j][0] / 9)) {
				ccRet.ep[i] = j;
				ccRet.eo[i] = 1;
				break;
			}
		}
	}
}

function toFaceCube(cc){
	var c, e, f, i, j, n, ori, ts;
	f = createArray(54);
	ts = [85, 82, 70, 68, 76, 66];
	for (i = 0; i < 54; ++i) {
		f[i] = ts[~~(i / 9)];
	}
	for (c = 0; c < 8; ++c) {
		j = cc.cp[c];
		ori = cc.co[c];
		for (n = 0; n < 3; ++n)
			f[cornerFacelet[c][(n + ori) % 3]] = ts[~~(cornerFacelet[j][n] / 9)];
	}
	for (e = 0; e < 12; ++e) {
		j = cc.ep[e];
		ori = cc.eo[e];
		for (n = 0; n < 2; ++n)
			f[edgeFacelet[e][(n + ori) % 2]] = ts[~~(edgeFacelet[j][n] / 9)];
	}
	return String.fromCharCode.apply(null, f);
}

var Cnk, ckmv2, cornerFacelet, edgeFacelet, fact, move2str, permMult, std2ud, ud2std;

function initialize() {
	Util_$clinit();
	CubieCube_$clinit();
	CoordCube_$clinit();
	initMove();
	initSym();
	initFlipSym2Raw();
	initTwistSym2Raw();
	initPermSym2Raw();
	initFlipMove();
	initTwistMove();
	initUDSliceMoveConj();
	initCPermMove();
	initEPermMove();
	initMPermMoveConj();
	initRawSymPrun(UDSliceTwistPrun, 6, UDSliceMove, UDSliceConj, TwistMove, SymStateTwist, null, null, 3);
	initRawSymPrun(UDSliceFlipPrun, 6, UDSliceMove, UDSliceConj, FlipMove, SymStateFlip, null, null, 3);
	initRawSymPrun(MEPermPrun, 7, MPermMove, MPermConj, EPermMove, SymStatePerm, null, null, 4);
	initRawSymPrun(MCPermPrun, 10, MPermMove, MPermConj, CPermMove, SymStatePerm, e2c, ud2std, 4);
}

	var randomSource = Math;

	var initialized = false;

	function ini(iniRandomSource, statusCallback) {

		if (typeof statusCallback != "function") {
			statusCallback = function() {};
		}

		if (!initialized) {
//			var cur = +new Date;
			initialize();
			randomSource = iniRandomSource;
			search = new Search;
			initialized = true;
//			console.log(+new Date - cur);
		}
	}


// SCRAMBLERS

	function rn(n) {
		return ~~(randomSource.random() * n);
	}
	
	var search;
	
	function getRandomScramble() {
		ini(Math);
		var cperm, eperm = rn(479001600);
		do {
			cperm = rn(40320);
		} while ((getNParity(cperm,8) ^ getNParity(eperm,12)) != 0);
		var posit = toFaceCube(new CubieCube1(cperm, rn(2187), eperm, rn(2048)));
		var solution = $solution(search, posit);

		return solution;
	}
	
	function cntU(b){for(var c=0,a=0;a<b.length;a++)-1==b[a]&&c++;return c};
	
	function fixOri(arr, cntU, base) {
		var sum = 0;
		var idx = 0;
		for (var i=0; i<arr.length-1; i++) {
			if (arr[i] == -1) {
				if (cntU-- == 1) {
					arr[i] = ((base << 4) - sum) % base;
				} else {
					arr[i] = rn(base);
				}
			}
			sum += arr[i];
			idx *= base;
			idx += arr[i];
		}
		return idx;
	}
	
	function fixPerm(arr, cntU, parity) {
		var val = [0,1,2,3,4,5,6,7,8,9,10,11];
		for (var i=0; i<arr.length; i++) {
			if (arr[i] != -1) {
				val[arr[i]] = -1;
			}
		}
		for (var i=0, j=0; i<val.length; i++) {
			if (val[i] != -1) {
				val[j++] = val[i];
			}
		}
		var last;
		for (var i=0; i<arr.length && cntU>0; i++) {
			if (arr[i] == -1) {
				var r = rn(cntU);
				arr[i] = val[r];
				for (var j=r; j<11; j++) {
					val[j] = val[j+1];
				}
				if (cntU-- == 2) {
					last = i;
				}
			}
		}
		if (getNParity(getNPerm(arr, arr.length), arr.length) == 1-parity) {
			var temp = arr[i-1];
			arr[i-1] = arr[last];
			arr[last] = temp;
		}
		return getNPerm(arr, arr.length);
	}
	
	function getAnyScramble(ep, eo, cp, co) {
		ini(Math);
		var neo = fixOri(eo, cntU(eo), 2);
		var nco = fixOri(co, cntU(co), 3);
		var nep, ncp;
		var ue = cntU(ep);
		var uc = cntU(cp);
		if (ue==0 && uc==0) {
			nep = getNPerm(ep, 12);
			ncp = getNPerm(cp, 8);
		} else if (ue!=0 && uc==0) {
			ncp = getNPerm(cp, 8);
			nep = fixPerm(ep, ue, getNParity(ncp, 8));
		} else if (ue==0 && uc!=0) {
			nep = getNPerm(ep, 12);
			ncp = fixPerm(cp, uc, getNParity(nep, 12));		
		} else {
			nep = fixPerm(ep, ue, -1);
			ncp = fixPerm(cp, uc, getNParity(nep, 12));		
		}
		var posit = toFaceCube(new CubieCube1(ncp, nco, nep, neo));
		var solution = $solution(search, posit);

		return solution;
	}

	function getEdgeScramble() {
		return getAnyScramble([-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],
			[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],[0,1,2,3,4,5,6,7],[0,0,0,0,0,0,0,0]);
	}

	function getCornerScramble() {
		return getAnyScramble([0,1,2,3,4,5,6,7,8,9,10,11],
			[0,0,0,0,0,0,0,0,0,0,0,0],[-1,-1,-1,-1,-1,-1,-1,-1],[-1,-1,-1,-1,-1,-1,-1,-1]);
	}

	function getLLScramble() {
		return getAnyScramble([-1,-1,-1,-1,4,5,6,7,8,9,10,11],
			[-1,-1,-1,-1,0,0,0,0,0,0,0,0],[-1,-1,-1,-1,4,5,6,7],[-1,-1,-1,-1,0,0,0,0]);
	}

	function getLSLLScramble() {
		return getAnyScramble([-1,-1,-1,-1,4,5,6,7,-1,9,10,11],
			[-1,-1,-1,-1,0,0,0,0,-1,0,0,0],[-1,-1,-1,-1,-1,5,6,7],[-1,-1,-1,-1,-1,0,0,0]);
	}

	function getF2LScramble() {
		return getAnyScramble([-1,-1,-1,-1,4,5,6,7,-1,-1,-1,-1],
			[-1,-1,-1,-1,0,0,0,0,-1,-1,-1,-1],[-1,-1,-1,-1,-1,-1,-1,-1],[-1,-1,-1,-1,-1,-1,-1,-1]);
	}

	function getZBLLScramble() {
		return getAnyScramble([-1,-1,-1,-1,4,5,6,7,8,9,10,11],
			[0,0,0,0,0,0,0,0,0,0,0,0],[-1,-1,-1,-1,4,5,6,7],[-1,-1,-1,-1,0,0,0,0]);
	}

	function getLSEScramble() {
		switch (rn(4)) {
			case 0: return getAnyScramble([-1,-1,-1,-1,4,-1,6,-1,8,9,10,11],[-1,-1,-1,-1,0,-1,0,-1,0,0,0,0],[0,1,2,3,4,5,6,7],[0,0,0,0,0,0,0,0]);
			case 1: return getAnyScramble([11,-1,10,-1,8,-1,9,-1,0,2,-1,-1],[0,-1,0,-1,0,-1,0,-1,0,0,-1,-1],[3,2,6,7,0,1,5,4],[2,1,2,1,1,2,1,2])+"x'";
			case 2: return getAnyScramble([4,-1,6,-1,-1,-1,-1,-1,11,10,9,8],[0,-1,0,-1,-1,-1,-1,-1,0,0,0,0],[7,6,5,4,3,2,1,0],[0,0,0,0,0,0,0,0])+"x2";
			case 3: return getAnyScramble([8,-1,9,-1,11,-1,10,-1,-1,-1,2,0],[0,-1,0,-1,0,-1,0,-1,-1,-1,0,0],[4,5,1,0,7,6,2,3],[2,1,2,1,1,2,1,2])+"x";
		}
	}

	function getCMLLScramble() {
		switch (rn(4)) {
			case 0: return getAnyScramble([-1,-1,-1,-1,4,-1,6,-1,8,9,10,11],[-1,-1,-1,-1,0,-1,0,-1,0,0,0,0],[-1,-1,-1,-1,4,5,6,7],[-1,-1,-1,-1,0,0,0,0]);
			case 1: return getAnyScramble([11,-1,10,-1,8,-1,9,-1,0,2,-1,-1],[0,-1,0,-1,0,-1,0,-1,0,0,-1,-1],[3,2,-1,-1,0,1,-1,-1],[2,1,-1,-1,1,2,-1,-1])+"x'";
			case 2: return getAnyScramble([4,-1,6,-1,-1,-1,-1,-1,11,10,9,8],[0,-1,0,-1,-1,-1,-1,-1,0,0,0,0],[7,6,5,4,-1,-1,-1,-1],[0,0,0,0,-1,-1,-1,-1])+"x2";
			case 3: return getAnyScramble([8,-1,9,-1,11,-1,10,-1,-1,-1,2,0],[0,-1,0,-1,0,-1,0,-1,-1,-1,0,0],[-1,-1,1,0,-1,-1,2,3],[-1,-1,2,1,-1,-1,1,2])+"x";
		}
	}

	function getCLLScramble() {
		return getAnyScramble([0,1,2,3,4,5,6,7,8,9,10,11],[0,0,0,0,0,0,0,0,0,0,0,0],[-1,-1,-1,-1,4,5,6,7],[-1,-1,-1,-1,0,0,0,0]);
	}

	function getELLScramble() {
		return getAnyScramble([-1,-1,-1,-1,4,5,6,7,8,9,10,11],[-1,-1,-1,-1,0,0,0,0,0,0,0,0],[0,1,2,3,4,5,6,7],[0,0,0,0,0,0,0,0]);
	}

	return {
		/* mark2 interface */
		getRandomScramble: getRandomScramble,//getRandomScramble,

		/* added methods */
		getEdgeScramble: getEdgeScramble,
		getCornerScramble: getCornerScramble,
		getLLScramble: getLLScramble,
		getLSLLScramble: getLSLLScramble,
		getZBLLScramble: getZBLLScramble,
		getF2LScramble: getF2LScramble,
		getLSEScramble: getLSEScramble,
		getCMLLScramble: getCMLLScramble,
		getCLLScramble: getCLLScramble,
		getELLScramble: getELLScramble,
		getAnyScramble: getAnyScramble
	};

})();