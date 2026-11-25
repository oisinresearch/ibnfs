\\ ============================================================================
\\ Polynomial Selection Helpers
\\ ============================================================================

getdiscpolyf(n, m, d, s = 1) =
{
  my(L = matid(d + 1), f);
  L[1, ] = vector(d + 1, i, (i - 2) * lift(Mod(m, n)^(i - 1)));
  L[2, ] = vector(d + 1, i, -(i - 1) * lift(Mod(m, n)^(i - 2)));
  L[1, 1] = n;
  L[2, 2] = n;
  L = matdiagonal(vector(d + 1, i, s^(i - 1))) * L;
  L *= qflll(L);
  L = matdiagonal(vector(d + 1, i, s^(1 - i))) * L;
  f = sum(i = 0, d, L[i + 1, 1] * x^i);
  if(pollead(f) < 0, f = -f);
  return(f);
}

getmonicdiscpoly(n, m, d, s = 1, bound = 0) =
{
  my(B, t, D, M, G, v, R, u, b0, lim, res, V, best, cur, c);
  t = vectorv(d, i,
    if(i == 1, lift((d - 1) * Mod(m, n)^d),
       i == 2, lift(-d * Mod(m, n)^(d - 1)), 0));
  if(t == 0, return(x^d));
  B = matid(d);
  B[1, 1] = n; B[2, 2] = n;
  for(i = 3, d,
    B[1, i] = lift((i - 2) * Mod(m, n)^(i - 1));
    B[2, i] = lift(-(i - 1) * Mod(m, n)^(i - 2));
  );
  D = matdiagonal(vector(d, i, s^(i - 1)));
  B *= qflll(D * B);
  M = D * B;
  G = M~ * M;
  v = matsolve(B, t);
  R = qfgaussred(G);
  u = vectorv(d);
  forstep(i = d, 1, -1,
    u[i] = round(v[i] + sum(j = i + 1, d, R[i, j] * (v[j] - u[j]))));
  b0 = norml2(M * (v - u));
  if(b0 == 0, return(x^d));
  lim = if(bound > 0 && bound < b0, bound + 1/2, b0);
  res = qfcvp(G, v, lim);
  V = res[3];
  best = b0;
  for(k = 1, matsize(V)[2],
    cur = norml2(M * (v - V[, k]));
    if(cur < best, best = cur; u = V[, k]);
  );
  if(bound > 0 && best > bound, return(0));
  c = t - B * u;
  return(x^d + sum(i = 0, d - 1, c[i + 1] * x^i));
}

getindexpolyf(n, m, d, s = 1) =
{
  my(L = matid(d), S, Si, t = vectorv(d), r, c1, c0);
  L[1, 1] = n^2;
  L[1, 2] = -n * (m % n);
  L[2, 2] = n;
  for(i = 3, d,
    c1 = lift(Mod(-(i - 1) * Mod(m, n)^(i - 2), n));
    c0 = lift(Mod(-Mod(m, n^2)^(i - 1) - c1 * m, n^2));
    L[1, i] = c0; L[2, i] = c1;
  );
  c1 = lift(Mod(-d * Mod(m, n)^(d - 1), n));
  c0 = lift(Mod(-Mod(m, n^2)^d - c1 * m, n^2));
  t[1] = c0; t[2] = c1;
  S  = matdiagonal(vector(d, i, s^(i - 1)));
  Si = matdiagonal(vector(d, i, s^(1 - i)));
  L  = Si * (S * L * qflll(S * L));
  r  = t - L * round(matsolve(L, t));
  return(x^d + sum(i = 0, d - 1, r[i + 1] * x^i));
}

getindexpolyflat(d, B, aut = 1, exact_ok = 0) =
{
  my(dm, g, b, r, k, m, a, P, f, M, n, tries = 0, J, Jnum, Jden, p, L, comp);
  if(aut < 1 || d % aut != 0, error("aut must be >= 1 and divide d"));
  dm = d / aut;
  if(dm == 1, error("need d/aut >= 2 for nontrivial index"));

  if(aut == 2, Jnum = x^2 + 1; Jden = x;
  , aut == 3,  Jnum = x^3 - 3*x - 1; Jden = x * (x + 1);
  , aut == 4,  Jnum = x^4 - 6*x^2 + 1; Jden = x * (x^2 - 1);
  , aut == 6,
    J = (x^3 - 3*x - 1) / (x * (x + 1));
    J = (J + subst(J, x, (x - 1) / (x + 2))) / 2;
    Jnum = numerator(J); Jden = denominator(J);
  , aut > 1,
    p = aut + 1; while(!isprime(p), p += aut);
    L = polsubcyclo(p, aut);
  );

  g = x^dm - sum(i = 0, dm - 1, x^i);
  b = Mod(x, g);
  r = polrootsreal(g, [1, 2])[1];
  k = if(aut == 1 || aut == 2 || aut == 3 || aut == 4 || aut == 6,
         max(1, floor(log(B) / log(r))),
         max(1, floor(log(B) / (aut * log(r)))));

  while(1,
    m = min(k, 40);
    a = Mod(1, g);
    for(j = 1, m, a = a * b + (random(3) - 1));
    a = a * b^(k - m) + Mod(sum(j = 0, dm - 1, (random(3) - 1) * x^j), g);
    P = charpoly(a);
    if(aut == 1, f = P;
    , aut == 2 || aut == 3 || aut == 4 || aut == 6,
      f = sum(i = 0, dm, polcoef(P, i) * Jnum^i * Jden^(dm - i));
    ,
      comp = polcompositum(P, L);
      f = comp[1];
      if(poldegree(f) != d, tries++; next);
    );
    if(vecmax(abs(Vec(f))) <= B && polisirreducible(f),
      M = matrix(dm, dm, i, j, polcoef(lift(a^(j - 1)), i - 1));
      n = abs(matdet(M));
      if(n > 0, break);
    );
    tries++;
    if(tries % 5 == 0 && k > 1, k--);
  );
  n = if(exact_ok, nfinit(f).index, n^aut);
  return([f, n]);
}

make_16_9_lll(p, d, s = 1) =
{
  my(m, f, n);
  while(1,
    m = 1 + random(p^2 - 1);
    f = getindexpolyf(p, m, d, s);
    if(polisirreducible(f),
      n = abs(poldisc(f));
      if(n % p^2 == 0, return([f, n, p, n / p^2]));
    );
  );
}

make_16_9_bal(d, B0) =
{
  my(g, b, a, f, M, p, q, n, a2, a1, a0);
  if(d < 3, error("need d >= 3"));
  while(1,
    g = x^d + sum(k = 1, d, (random(2 * B0^k + 1) - B0^k) * x^(d - k));
    if(polcoef(g, 0) != 0 && polisirreducible(g), break);
  );
  b = Mod(x, g);
  while(1,
    a2 = random(2 * B0 + 1) - B0;
    a1 = random(2 * B0^2 + 1) - B0^2;
    a0 = random(2 * B0^3 + 1) - B0^3;
    a  = b^3 + a2 * b^2 + a1 * b + a0;
    f  = charpoly(a, x);
    M  = matrix(d, d, i, j, polcoef(lift(a^(j - 1)), i - 1));
    p  = abs(matdet(M));
    if(p > 1 && polisirreducible(f), break);
  );
  q = abs(poldisc(g));
  n = p^2 * q;
  return([f, n, p, q]);
}

\\ ============================================================================
\\ Core Helpers (Sieve, Factor Bookkeeping, Blind Hensel Square Root)
\\ ============================================================================

poly_gcd_mod(A, B, n, v) =
{
  my(lc, g, inv, sh, R);
  A = lift(Mod(1, n) * A);
  B = lift(Mod(1, n) * B);
  while(B != 0,
    lc = pollead(B, v);
    g = gcd(lc, n);
    if(g > 1 && g < n, return([0, g]));
    inv = lift(Mod(lc, n)^(-1));
    B = lift(Mod(1, n) * (B * inv));
    R = A;
    while(R != 0 && poldegree(R, v) >= poldegree(B, v),
      sh = poldegree(R, v) - poldegree(B, v);
      R = lift(Mod(1, n) * (R - pollead(R, v) * v^sh * B));
    );
    A = B; B = R;
  );
  if(A == 0, return([0, n]));
  lc = pollead(A, v);
  g = gcd(lc, n);
  if(g > 1 && g < n, return([0, g]));
  inv = lift(Mod(lc, n)^(-1));
  return([1, lift(Mod(1, n) * (A * inv))]);
}

homog_norm(cvec, a, b) =
{
  my(d = #cvec - 1, s = cvec[1], bp = 1);
  for(k = 2, d + 1, bp *= b; s = s * a + cvec[k] * bp);
  return(s);
}

check_ab(a, b, cvec, B, n) =
{
  if(gcd(a, b) != 1, return([0, 0, 0, 1]));
  my(N = homog_norm(cvec, a, b), Nabs = abs(N), g, fa);
  if(Nabs == 0, return([0, 0, 0, 1]));
  g = gcd(Nabs, n);
  if(g > 1, return([if(g < n, 2, 0), 0, 0, g]));
  if(Nabs == 1, return([1, matrix(0, 2), sign(N), 1]));
  fa = factor(Nabs, B);
  if(vecmax(fa[, 1]) <= B, return([1, fa, sign(N), 1]));
  return([0, 0, 0, 1]);
}

sieve_line(b, a_lo, a_hi, k_split, sp, sr, sl, ns, cvec, r_real, B, n, SCALE, BLK, slack, root_drop, cap) =
{
  my(L = a_hi - a_lo + 1, S = vectorsmall(L), pk, lp, st);
  for(k = 1, k_split,
    pk = sp[k];
    if(b >= pk && b % pk == 0, next);
    lp = sl[k];
    st = (b * sr[k] - a_lo) % pk + 1;
    forstep(i = st, L, pk, S[i] += lp);
  );
  for(k = k_split + 1, ns,
    pk = sp[k];
    if(b >= pk && b % pk == 0, next);
    st = (b * sr[k] - a_lo) % pk + 1;
    if(st <= L, S[st] += sl[k]);
  );

  my(out_rels = List(), out_facs = List(), tested = 0, r1 = #r_real);
  my(br = vector(r1, j, b * r_real[j]));

  for(j = 1, r1,
    my(ar = round(br[j]));
    for(off = -2, 2,
      my(aa = ar + off);
      if(aa >= a_lo && aa <= a_hi && S[aa - a_lo + 1] >= 0,
        S[aa - a_lo + 1] = -1;
        if(gcd(aa, b) == 1,
          tested++;
          my(ck = check_ab(aa, b, cvec, B, n));
          if(ck[1] == 1,
            listput(out_rels, [aa, b, ck[2], ck[3]]);
            if(#out_rels >= cap, return([Vec(out_rels), tested, Vec(out_facs)]));
          , ck[1] == 2, listput(out_facs, ck[4]));
        );
      );
    );
  );

  forstep(i0 = 1, L, BLK,
    my(i1 = min(L, i0 + BLK - 1), a0 = a_lo + i0 - 1, a1 = a_lo + i1 - 1);
    my(am = (a0 + a1) \ 2);
    my(Nmin = min(abs(homog_norm(cvec, a0, b)),
              min(abs(homog_norm(cvec, a1, b)), abs(homog_norm(cvec, am, b)))));
    my(thr = if(Nmin <= 1, 0, max(0, round(SCALE * log(Nmin)) - slack)));
    for(j = 1, r1, if(br[j] >= a0 - 2 && br[j] <= a1 + 2, thr = max(0, thr - root_drop)));
    for(i = i0, i1,
      if(S[i] >= thr,
        my(aa = a_lo + i - 1);
        if(gcd(aa, b) == 1,
          tested++;
          my(ck = check_ab(aa, b, cvec, B, n));
          if(ck[1] == 1,
            listput(out_rels, [aa, b, ck[2], ck[3]]);
            if(#out_rels >= cap, return([Vec(out_rels), tested, Vec(out_facs)]));
          , ck[1] == 2, listput(out_facs, ck[4]));
        );
      );
    );
  );
  return([Vec(out_rels), tested, Vec(out_facs)]);
}

sieve_rect(b_lo, b_hi, a_lo, a_hi, k_split, sp, sr, sl, ns, cvec, r_real, B, n, SCALE, BLK, slack, root_drop, cap, label, t_s0, so_far, need, prev_tested) =
{
  my(out_rels = List(), out_facs = List(), tested = 0, t_last = getwalltime());
  for(b = b_lo, b_hi,
    my(rem = cap - #out_rels);
    if(rem <= 0, break);
    my(out = sieve_line(b, a_lo, a_hi, k_split, sp, sr, sl, ns, cvec, r_real, B, n, SCALE, BLK, slack, root_drop, rem));
    tested += out[2];
    for(i = 1, #out[1], listput(out_rels, out[1][i]));
    for(i = 1, #out[3], listput(out_facs, out[3][i]));
    if(getwalltime() - t_last >= 1500,
      t_last = getwalltime();
      printf("[sieve] %s b=%d/%d | rels=%d/%d | tested=%d | %.1fs\n",
        label, b, b_hi, so_far + #out_rels, need, prev_tested + tested, (t_last - t_s0) / 1000.0);
    );
  );
  return([Vec(out_rels), tested, Vec(out_facs)]);
}

refine_factors(L, g) =
{
  my(out, d, e, r, changed = 1);
  if(g > 1,
    out = List();
    for(i = 1, #L,
      d = gcd(L[i], g);
      if(d > 1 && d < L[i], listput(out, d); listput(out, L[i] / d), listput(out, L[i]));
    );
    L = Vec(out);
  );
  while(changed,
    changed = 0;
    out = List();
    for(i = 1, #L,
      if(e = ispower(L[i], , &r),
        for(k = 1, e, listput(out, r)); changed = 1;
      , listput(out, L[i]));
    );
    L = Vec(out);
    for(i = 1, #L,
      for(j = i + 1, #L,
        d = gcd(L[i], L[j]);
        if(d > 1 && (d < L[i] || d < L[j]),
          out = List();
          for(k = 1, #L,
            if(k == i && d < L[i], listput(out, d); listput(out, L[i] / d),
               k == j && d < L[j], listput(out, d); listput(out, L[j] / d),
               listput(out, L[k]));
          );
          L = Vec(out); changed = 1; break(2);
        );
      );
    );
  );
  return(L);
}

group_factors(L) =
{
  my(s = vecsort(L), u = List(), e = List(), i = 1, j);
  while(i <= #s,
    j = i; while(j < #s && s[j + 1] == s[i], j++);
    listput(u, s[i]); listput(e, j - i + 1); i = j + 1;
  );
  return(matconcat([Col(Vec(u)), Col(Vec(e))]));
}

fmt_fa(fa, sgn) =
{
  my(nr = matsize(fa)[1], s = if(sgn < 0, "-", ""));
  if(nr == 0, return(concat(s, "1")));
  for(i = 1, nr,
    s = concat(s, strprintf("%d%s%s", fa[i, 1],
      if(fa[i, 2] > 1, strprintf("^%d", fa[i, 2]), ""),
      if(i < nr, " * ", "")));
  );
  return(s);
}

\\ Blind algebraic square root via inert-prime Newton lifting (works for any degree d).
\\ Recovers exact w(v) = +- f'(v) * sqrt(prod (a_i - b_i*v)) in Z[v].
blind_sqrt_hensel(f, fp, act_rels, e, q, v, log_W) =
{
  my(d = poldegree(f), K = max(4, ceil((log_W + log(4.0)) / log(q)) + 3), M = q^K);
  my(facs = List());
  for(i = 1, #e,
    if(!e[i], next);
    my(a = act_rels[i][1], b = act_rels[i][2]);
    listput(facs, Mod(1, M) * if(b == 0, a, a - b * v));
  );
  if(#facs == 0, return([0, 0]));

  \\ Balanced product tree for beta mod (q^K, f)
  my(L = Vec(facs), fM = Mod(1, M) * f);
  while(#L > 1,
    my(nxt = List());
    forstep(i = 1, #L, 2,
      if(i < #L, listput(nxt, (L[i] * L[i + 1]) % fM), listput(nxt, L[i]));
    );
    L = Vec(nxt);
  );
  my(beta_M = lift(L[1]));

  \\ Initial inverse square root in F_{q^d} = F_q[v]/(f)
  my(t = ffgen(Mod(1, q) * f, v));
  my(b0 = subst(Pol(lift(Mod(1, q) * beta_M), v), v, t) + 0 * t, r0);
  if(b0 == 0 || !issquare(b0, &r0), return([0, 0]));
  my(u = lift((r0^(-1)).pol));

  \\ Quadratic Newton lift: u <- u * (3 - beta * u^2) / 2 mod (q^prec, f)
  my(prec = 1);
  while(prec < K,
    prec = min(K, 2 * prec);
    my(m = q^prec, fm = Mod(1, m) * f, um = Mod(1, m) * u, bm = Mod(1, m) * beta_M);
    my(inv2 = (m + 1) \ 2);
    um = (um * ((3 - ((bm * ((um * um) % fm)) % fm)) * inv2)) % fm;
    u = lift(um);
  );

  \\ w(v) = f'(v) * beta * u mod (q^K, f), center-lifted to Z[v]
  my(wM = lift(((Mod(1, M) * fp) * ((Mod(1, M) * beta_M * (Mod(1, M) * u)) % fM)) % fM));
  my(half = M \ 2, w = 0);
  for(j = 0, d - 1,
    my(c = polcoef(wM, j, v));
    if(c > half, c -= M);
    if(c != 0 && log(abs(c)) > log_W + 2.0, return([0, 0]));
    w += c * v^j;
  );
  return([1, w]);
}

\\ ============================================================================
\\ Main Blind One-Sided Index-Form Factoring Routine (no bnfinit)
\\ ============================================================================

factorindex(f, B, n = 0, n_deps = 20) =
{
  my(t0 = getwalltime());
  my(v = variable(f), fp = deriv(f, v), d = poldegree(f));
  my(disc_f = poldisc(f), cvec = Vec(f));
  if(pollead(f) != 1, error("f must be monic"));
  if(!polisirreducible(f), error("f must be irreducible"));
  n = if(n == 0, abs(disc_f), abs(n));

  \\ 1. Roots, Lagrange bound constants C_j, inert prime q, and f'(v)^(-1) mod f
  my(r_all = polroots(f), r_real = polrootsreal(f), r1 = #r_real);
  my(logC = vector(d));
  for(j = 1, d,
    my(qv = vector(d), rj = r_all[j]);
    qv[1] = 1.0;
    for(k = 2, d, qv[k] = cvec[k] + rj * qv[k - 1]);
    logC[j] = log(vecmax(abs(qv)));
  );

  my(q_inert = nextprime(max(B + 100, 2^30)), q_tries = 0);
  while(n % q_inert == 0 || !polisirreducible(Mod(1, q_inert) * f),
    q_inert = nextprime(q_inert + 1);
    q_tries++;
    if(q_tries > 4000, error("no inert prime found (Galois group may lack a d-cycle)"));
  );

  my(fp_inv = lift(Mod(fp, f)^(-1)), D_fp = denominator(content(fp_inv)), P_fp = D_fp * fp_inv);

  \\ Optional blind double root m mod n (separate incidental GCDs from NFS splits)
  my(inc_facs = List(), has_m = 0, m = -1, n_m = n);
  my(gres = poly_gcd_mod(f, fp, n, v));
  if(gres[1] == 1 && poldegree(gres[2], v) == 1,
    m = (-polcoef(gres[2], 0, v)) % n; has_m = 1;
  , if(gres[1] == 0, listput(inc_facs, gres[2])));

  \\ 2. Local bad primes <= B (never factors n or global disc(f)) + FB + quadratic chars
  my(P_bad = List());
  forprime(ell = 2, B, if(n % ell != 0 && disc_f % ell == 0, listput(P_bad, ell)));
  P_bad = Vec(P_bad);
  my(nf_loc = if(#P_bad > 0, nfinit([f, P_bad]), 0));
  my(one_loc = if(#P_bad > 0, nfalgtobasis(nf_loc, 1), 0));
  my(alp_loc = if(#P_bad > 0, nfalgtobasis(nf_loc, v), 0));

  my(SCALE = 100, P_skip = if(B >= 1000, 7, 0));
  my(n_fb = 0, fb_unram = vector(B), fb_ram = vector(B), free_rels = List());
  my(spL = List(), srL = List(), slL = List());

  forprime(ell = 2, B,
    if(n % ell == 0, next);
    my(lp = round(SCALE * log(ell)));
    if(disc_f % ell != 0,
      my(rts = lift(polrootsmod(f, ell)), nr = #rts);
      if(nr == 0, next);
      my(rows = vector(nr));
      for(j = 1, nr,
        n_fb++; rows[j] = n_fb;
        if(ell > P_skip, listput(spL, ell); listput(srL, rts[j]); listput(slL, lp));
      );
      fb_unram[ell] = [rts, rows];
      if(nr == d, listput(free_rels, ell));
    ,
      my(prs = idealprimedec(nf_loc, ell), nr = #prs, rows = vector(nr));
      for(j = 1, nr, n_fb++; rows[j] = n_fb);
      fb_ram[ell] = [prs, rows];
      if(ell > P_skip,
        my(rts = lift(polrootsmod(f, ell)));
        for(j = 1, #rts, listput(spL, ell); listput(srL, rts[j]); listput(slL, lp));
      );
    );
  );

  my(n_qc = 32, qc_p = vector(n_qc), qc_r = vector(n_qc), k_qc = 0, pq = nextprime(B + 1));
  while(k_qc < n_qc,
    if(n % pq != 0 && disc_f % pq != 0,
      my(rts = lift(polrootsmod(f, pq)));
      for(j = 1, #rts,
        if(k_qc >= n_qc, break);
        k_qc++; qc_p[k_qc] = pq; qc_r[k_qc] = rts[j];
      );
    );
    pq = nextprime(pq + 1);
  );

  my(sp = Vecsmall(spL), sr = Vecsmall(srL), sl = Vecsmall(slL), ns = #sp);
  my(n_rows_est = n_fb + r1 + n_qc);
  my(need_sieved = max(10, n_rows_est + max(25, n_deps + 5) - #free_rels));

  printf("[setup] deg=%d, r1=%d | B=%d, #FB=%d, bad=%d, free=%d, qc=%d, need=%d (%.2fs)\n",
    d, r1, B, n_fb, #P_bad, #free_rels, n_qc, need_sieved, (getwalltime() - t0) / 1000.0);

  \\ 3. Expanding-shell one-sided line sieve
  my(c0 = abs(cvec[d + 1]), cd1 = abs(cvec[2]));
  my(skew = max(1.0, min(1000.0, (max(1, c0) / max(1, cd1))^(1.0 / (d - 1)))));
  for(j = 1, r1,
    if(abs(r_real[j]) >= 0.5 && abs(r_real[j]) <= 5.0,
      skew = max(skew, min(5.0, abs(r_real[j]) + 0.5))));

  my(BLK = 64, slack = round(SCALE * min(12.0, 0.7 * log(B) + if(P_skip > 0, 3.0, 1.5))));
  my(root_drop = round(SCALE * log(BLK)));
  my(rels = List(), t_s0 = getwalltime(), n_cands = 0);

  my(find_split = (L) -> my(lo = 0, hi = ns, mid);
    while(lo < hi, mid = (lo + hi + 1) \ 2; if(sp[mid] <= L, lo = mid, hi = mid - 1));
    return(lo));

  my(area0 = max(1500.0 * 400.0, max(need_sieved * 1200.0, (B / 8.0)^2)));
  my(A_cur = max(1500, min(40000, round(sqrt(area0 * skew)))));
  my(B_cur = max(200,  round(sqrt(area0 / skew))));
  my(A_prev = 0, B_prev = 0, shell = 0);

  while(#rels < need_sieved && shell < 8,
    shell++;
    my(rects = if(shell == 1,
      [[1, B_cur, -A_cur, A_cur, strprintf("shell %d (A=%d, B=%d)", shell, A_cur, B_cur)]],
      [[1, B_prev, -A_cur, -A_prev - 1, strprintf("shell %d L (A=%d, B=%d)", shell, A_cur, B_cur)],
       [1, B_prev, A_prev + 1, A_cur,   strprintf("shell %d R (A=%d, B=%d)", shell, A_cur, B_cur)],
       [B_prev + 1, B_cur, -A_cur, A_cur, strprintf("shell %d T (A=%d, B=%d)", shell, A_cur, B_cur)]]));
    for(ri = 1, #rects,
      if(#rels >= need_sieved, break);
      my(rc = rects[ri], ks = find_split(rc[4] - rc[3] + 1));
      my(out = sieve_rect(rc[1], rc[2], rc[3], rc[4], ks, sp, sr, sl, ns, cvec, r_real, B, n,
                          SCALE, BLK, slack, root_drop, need_sieved - #rels, rc[5], t_s0, #rels, need_sieved, n_cands));
      n_cands += out[2];
      for(i = 1, #out[1], listput(rels, out[1][i]));
      for(i = 1, #out[3], listput(inc_facs, out[3][i]));
    );
    printf("[sieve] shell %d done (A=%d, B=%d) | rels=%d/%d | tested=%d | %.2fs\n",
      shell, A_cur, B_cur, #rels, need_sieved, n_cands, (getwalltime() - t_s0) / 1000.0);
    A_prev = A_cur; B_prev = B_cur;
    A_cur *= 2; B_cur *= 2;
  );

  my(n_sieved = #rels);
  for(i = 1, #free_rels, listput(rels, [free_rels[i], 0, Mat([free_rels[i], d]), 1]));
  my(R = #rels, t_sieve = getwalltime() - t_s0);
  if(R <= n_rows_est, error("Not enough relations found for B=%d; increase B", B));

  \\ 4. Sparse odd-parity ideal lists + iterative singleton pruning
  my(t_la0 = getwalltime(), rel_odd = vector(R), fb_deg = vectorsmall(n_fb));
  for(col = 1, R,
    my(a = rels[col][1], b = rels[col][2], fa = rels[col][3], il = List());
    if(b == 0,
      my(rows = fb_unram[a][2]);
      for(j = 1, #rows, listput(il, rows[j]); fb_deg[rows[j]]++);
    ,
      my(elt_loc = 0);
      for(j = 1, matsize(fa)[1],
        my(ell = fa[j, 1], ev = fa[j, 2]);
        if(disc_f % ell != 0,
          if(ev % 2 == 0, next);
          my(uinfo = fb_unram[ell], rts = uinfo[1], rows = uinfo[2]);
          for(k = 1, #rts,
            if((a - b * rts[k]) % ell == 0, listput(il, rows[k]); fb_deg[rows[k]]++; break));
        ,
          if(elt_loc == 0, elt_loc = a * one_loc - b * alp_loc);
          my(rinfo = fb_ram[ell], prs = rinfo[1], rows = rinfo[2]);
          for(k = 1, #prs,
            if(idealval(nf_loc, elt_loc, prs[k]) % 2, listput(il, rows[k]); fb_deg[rows[k]]++));
        );
      );
    );
    rel_odd[col] = Vecsmall(il);
  );

  my(alive = vectorsmall(R, i, 1), pruned = 1);
  while(pruned,
    pruned = 0;
    for(col = 1, R,
      if(!alive[col], next);
      my(il = rel_odd[col], kill = 0);
      for(j = 1, #il, if(fb_deg[il[j]] == 1, kill = 1; break));
      if(kill,
        alive[col] = 0; pruned = 1;
        for(j = 1, #il, fb_deg[il[j]]--);
      );
    );
  );

  my(fb_map = vectorsmall(n_fb), n_fb_f = 0);
  for(j = 1, n_fb, if(fb_deg[j] > 0, n_fb_f++; fb_map[j] = n_fb_f));
  my(act_idx = List());
  for(col = 1, R, if(alive[col], listput(act_idx, col)));
  act_idx = Vecsmall(act_idx);
  my(R_f = #act_idx, n_rows = n_fb_f + r1 + n_qc);
  if(R_f <= n_rows, error("Not enough relations after pruning; increase B"));

  \\ 5. Build F_2 matrix (pruned FB + real signs + quadratic characters) and find kernel
  my(M = matrix(n_rows, R_f), act_rels = vector(R_f));
  for(c = 1, R_f,
    my(col = act_idx[c], a = rels[col][1], b = rels[col][2], il = rel_odd[col]);
    act_rels[c] = rels[col];
    for(j = 1, #il, M[fb_map[il[j]], c] = 1);
    if(b > 0,
      for(j = 1, r1, if(a - b * r_real[j] < 0, M[n_fb_f + j, c] = 1));
      for(k = 1, n_qc, if(kronecker(a - b * qc_r[k], qc_p[k]) == -1, M[n_fb_f + r1 + k, c] = 1));
    ,
      for(k = 1, n_qc, if(kronecker(a, qc_p[k]) == -1, M[n_fb_f + r1 + k, c] = 1));
    );
  );

  my(Kmat = lift(matker(M * Mod(1, 2))));
  my(n_ker = matsize(Kmat)[2]);
  my(weights = vector(n_ker, k, vecsum(Kmat[, k])));
  my(perm = vecsort(weights, , 1));
  printf("[linalg] pruned %dx%d -> %dx%d F_2 matrix -> ker_dim=%d (%.2fs)\n",
    n_rows_est, R, n_rows, R_f, n_ker, (getwalltime() - t_la0) / 1000.0);

  \\ 6. Blind Hensel square root & factor extraction
  my(t_sq0 = getwalltime(), nfs_facs = [n], n_sq = 0, n_splits = 0);
  my(max_test = min(n_ker, n_deps), fn = Mod(1, n) * f, fpn = Mod(1, n) * fp);
  my(fD = Mod(1, D_fp) * f, PD = Mod(1, D_fp) * P_fp);

  for(idx = 1, max_test,
    my(e = Kmat[, perm[idx]], lg_emb = vector(d));
    for(i = 1, R_f,
      if(!e[i], next);
      my(a = act_rels[i][1], b = act_rels[i][2]);
      if(b == 0,
        my(la = log(a));
        for(j = 1, d, lg_emb[j] += la);
      ,
        for(j = 1, d, lg_emb[j] += log(max(1e-30, abs(a - b * r_all[j]))));
      );
    );
    my(log_W = vecmax(vector(d, j, 0.5 * lg_emb[j] + logC[j])) + log(d) + 5.0);

    my(sq = blind_sqrt_hensel(f, fp, act_rels, e, q_inert, v, log_W));
    if(!sq[1], next);
    my(w = sq[2]);

    \\ Verify w^2 == f'^2 * beta mod (n, f)
    my(wn = Mod(1, n) * w, bn = Mod(1, n) * 1);
    for(i = 1, R_f,
      if(!e[i], next);
      my(a = act_rels[i][1], b = act_rels[i][2]);
      bn = (bn * if(b == 0, a, a - b * v)) % fn;
    );
    if(lift((wn * wn - ((fpn * fpn) % fn) * bn) % fn) != 0, next);
    n_sq++;

    \\ Blind extraction: power-basis denominator D(gamma) + derivative w'(m) if m exists
    my(cands = List());
    if(D_fp > 1,
      my(u_poly = lift(((Mod(1, D_fp) * w) * PD) % fD));
      my(D_gam = D_fp / gcd(content(u_poly), D_fp), g_den = gcd(D_gam, n));
      if(g_den > 1 && g_den < n, listput(cands, g_den));
    );
    if(has_m,
      my(g_w  = gcd(lift(subst(Mod(1, n_m) * w, v, Mod(m, n_m))), n_m));
      my(g_wp = gcd(lift(subst(Mod(1, n_m) * deriv(w, v), v, Mod(m, n_m))), n_m));
      if(g_w  > 1 && g_w  < n_m, listput(cands, g_w));
      if(g_wp > 1 && g_wp < n_m, listput(cands, g_wp));
    );

    if(#cands > 0,
      n_splits++;
      for(c = 1, #cands, nfs_facs = refine_factors(nfs_facs, cands[c]));
    );
  );

  printf("[sqrt] tested %d deps -> %d/%d squares, %d/%d split n (%.1f%%) (%.2fs)\n",
    max_test, n_sq, max_test, n_splits, n_sq,
    if(n_sq > 0, 100.0 * n_splits / n_sq, 0.0), (getwalltime() - t_sq0) / 1000.0);

  \\ 7. Honest final report (never claims success from incidental GCDs alone)
  my(t_tot = getwalltime() - t0, fmat = group_factors(nfs_facs));
  if(n_splits == 0,
    printf("\nFAILED: NFS square root produced 0 splits of n = %d (total %.2fs).\n", n, t_tot / 1000.0);
  ,
    printf("\nFactors of n = %d (total %.2fs):\n  ", n, t_tot / 1000.0);
    for(i = 1, matsize(fmat)[1],
      printf("%d%s%s%s", fmat[i, 1],
        if(fmat[i, 2] > 1, strprintf("^%d", fmat[i, 2]), ""),
        if(!isprime(fmat[i, 1]), " [composite]", ""),
        if(i < matsize(fmat)[1], " * ", "\n"));
    );
  );
  if(#inc_facs > 0,
    my(u_inc = Set(Vec(inc_facs)));
    printf("  [note: incidental sieve/setup GCD(s) observed (not used above): %Ps]\n", u_inc);
  );

  my(n_show = min(10, R), top10 = vector(n_show));
  printf("\nFirst %d full relations:\n", n_show);
  for(i = 1, n_show,
    my(a = rels[i][1], b = rels[i][2], fa = rels[i][3], sg = rels[i][4]);
    top10[i] = [a, b, fa];
    if(b == 0,
      printf("  [%2d] free prime (%d)       | N = %s\n", i, a, fmt_fa(fa, sg));
    ,
      printf("  [%2d] (a, b) = (%7d, %4d) | N = %s\n", i, a, b, fmt_fa(fa, sg));
    );
  );

  return([fmat, top10, [B, n_fb, R, R_f, n_sieved, #free_rels, n_ker, max_test, n_sq, n_splits, t_sieve, t_tot]]);
}

