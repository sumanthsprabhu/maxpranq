#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"
#include <fstream>

using namespace std;
using namespace boost;

namespace ufo
{
  static void getCombinations(vector<vector<int>>& in, vector<vector<int>>& out, int pos = 0)
  {
    if (pos == 0) out.push_back(vector<int>());
    if (pos == in.size()) return;

    vector<vector<int>> out2;

    for (auto & a : in[pos])
    {
      for (auto & b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};
  
  void
  computetime(const string & msg, clock_t & start)
  {
    outs() << msg << " " << (clock() - start)/(CLOCKS_PER_SEC/1000.0) << endl;
    start = clock();
  }
  
  class NonlinCHCsolver
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;
    bool hasArrays = false;
    ExprSet declsVisited;
    map<HornRuleExt*, vector<ExprVector>> abdHistory;
    int globalIter = 0;
    int strenBound;
    bool debug = false;
    vector<int> propOrder;
    map<pair<int, Expr>, ExprVector> invItrs;
    map<Expr, ExprVector> invSizeVars;
    map<Expr, bool> invItrInc;
    
    map<int, vector<int>> nondetChcPair;
    map<int, Expr> nondetChcGuard;

    bool dumpsmt;
    
    public:

    NonlinCHCsolver (CHCs& r, int _b) : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b), dumpsmt(false) {}

    bool checkAllOver (bool checkQuery = false, bool printModel = false, bool nondet = false)
    {
      outs () << " checkAllOver\n";
      for (int hrIndex = 0; hrIndex < ruleManager.chcs.size(); hrIndex++)
      {
        auto & hr = ruleManager.chcs[hrIndex];
        if (hr.isQuery && !checkQuery) continue;
        if (printModel) {
          outs() << *(hr.body) << endl;
        }
        if (!checkCHC(hr, candidates, printModel, nondet, hrIndex)) return false;
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations, bool printModel = false, bool nondet = false, int hrIndex = -1)
    {
      outs () << " check chc: ";
      ExprSet checkList;
      checkList.insert(hr.body);
      if (nondet && hrIndex != -1) {
        auto itr = nondetChcGuard.find(hrIndex);
        if (itr != nondetChcGuard.end()) {
          checkList.insert(itr->second);
        }
      }
      Expr rel;
      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        Expr rel = hr.srcRelations[i];
        outs () << rel << " ";
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        outs () << " -> " << rel << "\n";
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        checkList.insert(disjoin(negged, m_efac));
      }
      else
      {
        outs () << " -> false\n";
      }
      boost::tribool res = u.isSat(checkList);
      if (res && printModel) {
        outs() << "Model: " << *(u.getModel()) << endl;
      }
      return bool(!res);
    }

    void shrinkCnjs(ExprSet & cnjs)
    {
      ExprSet shrunk;
      ExprSet cnjsTmp = cnjs;
      for (auto c1 = cnjsTmp.begin(); c1 != cnjsTmp.end(); ++c1)
      {
        if (isOpX<OR>(*c1)) continue;
        for (auto c2 = cnjs.begin(); c2 != cnjs.end();)
        {
          if (!isOpX<OR>(*c2)) { ++c2; continue; };
          ExprSet dsjs;
          ExprSet newDsjs;
          getDisj(*c2, dsjs);
          for (auto & d : dsjs)
            if (u.isSat(*c1, d))
              newDsjs.insert(d);
          shrunk.insert(disjoin(newDsjs, m_efac));
          c2 = cnjs.erase(c2);
          cnjs.insert(disjoin(newDsjs, m_efac));
        }
        cnjs.insert(shrunk.begin(), shrunk.end());
        shrunk.clear();
      }
    }

    void preproGuessing(Expr e, ExprVector& varsToKeep, ExprVector& varsToRename,
                        ExprSet& guesses, bool backward = false, bool mutate = true)
    {
      if (!u.isSat(e)) return;
      if (!containsOp<FORALL>(e) && !containsOp<EXISTS>(e)) e = rewriteSelectStore(e);

      ExprSet qVars, varsToElim, complex;
      ExprMap repls, replsRev;
      map<Expr, ExprSet> replIngr;

      getQuantifiedVars(e, qVars);
      filter (e, bind::IsConst (), inserter (varsToElim, varsToElim.begin()));
      minusSets(varsToElim, varsToKeep);
      minusSets(varsToElim, qVars);
      findComplexNumerics(e, complex);

      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
                                   ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);
      // eTmp = replaceQVars(eTmp, repls);
      if (backward && (containsOp<FORALL>(e) || containsOp<EXISTS>(e)))
      {
        eTmp = replaceAll (eTmp, replsRev);
        eTmp = simplifyQuants(eTmp);
        // eTmp = simplifyExists(eTmp);
        eTmp = u.removeRedundantConjuncts(eTmp);
        eTmp = simplifyBool(eTmp);
        eTmp = u.extendQuantified(eTmp);
        // eTmp = moveInsideQuantifiers(eTmp);
        map<Expr, ExprVector> qv;
        getQVars (eTmp, qv);

        for (auto tq : qv)
        {
          Expr q = tq.first;
          Expr ep = q->last();
          ep = simpleQE(ep, varsToElim);
          ep = rewriteSelectStore(ep);
          ep = eliminateQuantifiersRepl(ep, varsToElim);
          ep = u.removeRedundantDisjuncts(ep);
          ep = simplifyBool(simplifyArithm(ep));
          if (isOpX<FALSE>(ep) || isOpX<TRUE>(ep))
          {
            eTmp = replaceAll(eTmp, q, ep);
            continue;
          }
          ExprSet epCnjs;
          getConj(ep, epCnjs);

          for (auto & v : varsToKeep)
          {
            ExprSet tmpm;
            for (auto & p : epCnjs)
              if (contains(p, v) && !containsOp<ARRAY_TY>(p))
                tmpm.insert(p);

            if (isNumeric(v))
            {
              ExprSet tmp = {v};
              epCnjs.insert(eliminateQuantifiers(conjoin(tmpm, m_efac), tmp));
            }
          }

          Expr toReplace = conjoin(epCnjs, m_efac);
          if (emptyIntersect(toReplace, tq.second))
            eTmp = replaceAll(eTmp, q, toReplace);
          else
            eTmp = replaceAll(eTmp, q->last(), toReplace);   // TODO: multiple things
        }
        // eTmp = moveInsideQuantifiers(eTmp);
      }
      else
      {
        varsToElim.clear();
        filter (eTmp, bind::IsConst (), inserter (varsToElim, varsToElim.begin())); // prepare vars
        for (auto it = varsToElim.begin(); it != varsToElim.end(); )
        {
          if (find(varsToKeep.begin(), varsToKeep.end(), *it) != varsToKeep.end() ||
              find(qVars.begin(), qVars.end(), *it) != qVars.end())
          it = varsToElim.erase(it);
          else
          {
            Expr tmp = replsRev[*it];
            if (tmp == NULL) ++it;
            else
            {
              ExprSet tmpSet = replIngr[*it];
              minusSets(tmpSet, varsToKeep);
              minusSets(tmpSet, qVars);
              if (tmpSet.empty()) it = varsToElim.erase(it);
              else ++it;
            }
          }
        }
      }

      outs() << "eTmp: ";
      pprint(eTmp);
      outs() << "\nto elim: ";
      pprint(varsToElim);
      outs () << "\n";

      eTmp = eliminateQuantifiers(eTmp, varsToElim);
      outs () << "  res = " << eTmp << "\n";
      if (backward) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(simplifyArithm(eTmp, false, true));

      ExprSet tmp;

      if (mutate)
        mutateHeuristic(eTmp, tmp);
      else
        getConj(eTmp, tmp);

      for (auto g : tmp)
      {
        g = replaceAll (g, replsRev);
        // g = simplifyBool(simplifyExists(simplifyQuants(g)));
        if (!varsToRename.empty())
          g = replaceAll(g, varsToKeep, varsToRename);
        guesses.insert(g);
      }
    }

    // search for a CHC having the form r1 /\ .. /\ rn => rel, where rel \not\in {r1, .., rn}
    bool hasNoDef(Expr rel)
    {
      for (auto & hr : ruleManager.chcs)
        if (hr.dstRelation == rel &&
          find (hr.srcRelations.begin(), hr.srcRelations.end(), rel) == hr.srcRelations.end())
            return false;
      return true;
    }

    // lightweight (non-inductive) candidate propagation both ways
    // subsumes bootstrapping (ssince facts and queries are considered)
    void propagate(bool fwd = true)
    {
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
        bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation));
        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

        if (fwd && srcVisited && !dstVisited)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
      }

      if (declsVisited.size() != szInit) propagate(fwd);
    }

    void propagateCandidatesForward(HornRuleExt& hr)
    {
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery) return;

        Expr body = getQuantifiedCands(true, hr);

        ExprSet all;
        all.insert(body);
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          if (!hasArrays) // we need "clean" invariants in the case of arrays (to be used as ranges)
          {
            // currently, tries all candidates; but in principle, should try various subsets
            for (auto & c : candidates[rel])
              all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars[i]));
          }
        }

        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);

        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr, bool forceConv = false)
    {
        if (hr.isFact) return;

        Expr dstRel = hr.dstRelation;
        ExprVector& rels = hr.srcRelations;

        // identifying nonlinear cases (i.e., when size(occursNum[...]) > 1)
        map<Expr, set<int>> occursNum;
        for (int i = 0; i < rels.size(); i++)
        {
          occursNum[rels[i]].insert(i);
          for (int j = i+1; j < rels.size(); j++)
            if (rels[i] == rels[j])
              occursNum[rels[i]].insert(j);
        }

        ExprVector invVars, srcVars;
        for (int i = 0; i < hr.srcVars.size(); i++)
          srcVars.insert(srcVars.end(), hr.srcVars[i].begin(), hr.srcVars[i].end());

        if (hr.srcVars.size() == 1) invVars = ruleManager.invVars[rels[0]];

        propagateRangeBackward(hr, srcVars, invVars);

        ExprSet cands;
        if (hr.isQuery)
          cands.insert(mk<FALSE>(m_efac));
        else cands.insert(simplifyBool(conjoin(candidates[dstRel], m_efac)));

        ExprSet mixedCands;
        ExprVector curCnd;

        for (int i = 0; i < rels.size(); i++)
        {
          ExprSet tmp;
          getConj(replaceAll(conjoin(candidates[rels[i]], m_efac),
                             ruleManager.invVars[rels[i]], hr.srcVars[i]), tmp);
          curCnd.push_back(conjoin(tmp, m_efac));
        }

        // actually, just a single candidate, in the most recent setting;
        // TODO: remove the loop (or find use of it)
        for (auto & c : cands)
        {
          ExprSet all, newCnd;
          all.insert(hr.body);
          all.insert(mkNeg(replaceAll(c, ruleManager.invVars[dstRel], hr.dstVars)));
          all.insert(curCnd.begin(), curCnd.end());

          // TODO: add more sophisticated blocking based on unsuccessful tries from abdHistory
          preproGuessing(conjoin(all, m_efac), srcVars, invVars, newCnd, true, false);

          if (!(u.isSat(conjoin(curCnd, m_efac), conjoin(newCnd, m_efac))))
          {
            // simple heuristic: find if some current guess was already created by abduction
            // then, delete it and try again
            if (!hr.isInductive)
              for (auto & t : abdHistory[&hr])
                for (int j = 0; j < t.size(); j++)
                  if (u.implies(conjoin(candidates[rels[j]], m_efac), t[j]))
                    candidates[rels[j]].clear();
            continue;
          }

          // oftentimes, newCnd is a disjunction that can be simplified
          // by considering other candidates in curCnd
          ExprSet tmp, tmp2;
          for (auto c : newCnd) getConj(c, tmp);
          for (auto c : curCnd) getConj(c, tmp);
          shrinkCnjs(tmp);
          getConj(conjoin(tmp, m_efac), tmp2);
          ineqMerger(tmp2, true);
          simplifyPropagate(tmp2);
          Expr stren = simplifyArithm(conjoin(tmp2, m_efac));
          mixedCands.insert(stren);
        }

        if (hr.srcVars.size() == 1)
        {
          if (forceConv) forceConvergence(candidates[rels[0]], mixedCands);
          for (auto & m : mixedCands) getConj(m, candidates[rels[0]]);
        }
        else
        {
          decompose(hr, curCnd, occursNum, mixedCands);
        }
      }

    void decompose(HornRuleExt& hr, ExprVector& curCnd, map<Expr, set<int>>& occursNum, ExprSet& mixedCands)
    {
          Expr dstRel = hr.dstRelation;
          ExprVector& rels = hr.srcRelations;
          // decomposition here

          // fairness heuristic: prioritize candidates for all relations, which are true
          // TODO: find a way to disable it if for some reason some invariant should only be true
          vector<bool> trueCands;
          ExprSet trueRels;
          int numTrueCands = 0;
          for (int i = 0; i < rels.size(); i++)
          {
            trueCands.push_back(u.isTrue(curCnd[i]));
            if (trueCands.back())
            {
              trueRels.insert(rels[i]);
              numTrueCands++;
            }
          }

          // numTrueCands = 0;       // GF: hack to disable fairness

          ExprSet allGuessesInit;
          if (numTrueCands > 0)      // at least one curCnd should be true
            for (int i = 0; i < rels.size(); i++)
              if (!trueCands[i])
                allGuessesInit.insert(curCnd[i]);

          // actually, just a single candidate, in the most recent setting;
          // TODO: remove the loop (or find use of it)
          for (auto it = mixedCands.begin(); it != mixedCands.end(); )
          {
            Expr a = *it;
            ExprSet processed;
            ExprSet allGuesses = allGuessesInit;
            ExprVector histRec;

            auto candidatesTmp = candidates;

            for (int i = 0; i < rels.size(); i++)
            {
              // skip the relation if it already has a candidate and there exists a relation with no candidate
              // (existing candidates are already in allGuesses)
              if (numTrueCands > 0 && !trueCands[i]) continue;

              Expr r = rels[i];
              if (!u.isSat(a, conjoin(curCnd, m_efac))) return;  // need to recheck because the solver has been reset
              if (processed.find(r) != processed.end()) continue;

              ExprVector invVars;
              ExprSet backGuesses, allVarsExcept;
              ExprVector vars;
              for (int j = 0; j < rels.size(); j++)
              {
                Expr t = rels[j];
                if (processed.find(t) != processed.end()) continue;
                if (t == r)
                {
                  vars.insert(vars.begin(), hr.srcVars[j].begin(), hr.srcVars[j].end());
                  if (occursNum[r].size() == 1) invVars = ruleManager.invVars[rels[j]];
                }
                else
                {
                  for (auto & v : hr.srcVars[j])
                  if ((containsOp<ARRAY_TY>(a) && containsOp<ARRAY_TY>(v)) ||
                      !containsOp<ARRAY_TY>(a))
                  allVarsExcept.insert(v);
                }
              }

              // model-based cartesian decomposition
              ExprSet all = allGuesses;
              all.insert(mkNeg(a));

              if (trueRels.size() != 1)                  // again, for fairness heuristic:
                all.insert(u.getModel(allVarsExcept));

              // in the case of nonlin, invVars is empty, so no renaming happens:

              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                getConj(conjoin(backGuesses, m_efac), candidates[r]);
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
              }
              else
              {
                // nonlinear case; proceed to isomorphic decomposition for each candidate
                map<int, ExprVector> multiabdVars;

                for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                  for (auto & v : ruleManager.invVars[r])
                    multiabdVars[*it2].push_back(
                      cloneVar(v, mkTerm<string> (
                        "__multiabd_var" + lexical_cast<string>(*v) + "_" + to_string(*it2), m_efac)));

                Expr b = conjoin(backGuesses, m_efac);
                {
                  ExprSet sol;
                  int iter = 0;
                  while (++iter < 10 /*hardcode*/)
                  {
                    // preps for obtaining a new model

                    ExprSet cnj;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                    {
                      ExprSet dsj;
                      if (!sol.empty())
                        dsj.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      for (auto it3 = occursNum[r].begin(); it3 != occursNum[r].end(); ++it3)
                      {
                        ExprSet modelCnj;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          modelCnj.insert(mk<EQ>(hr.srcVars[*it2][i], multiabdVars[*it3][i]));
                        dsj.insert(conjoin(modelCnj, m_efac));
                      }
                      cnj.insert(disjoin(dsj, m_efac));
                    }

                    // obtaining a new model
                    ExprVector args;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      for (auto & v : hr.srcVars[*it2])
                        args.push_back(v->left());
                    args.push_back(mk<IMPL>(conjoin(cnj, m_efac), b));

                    ExprSet negModels;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      negModels.insert(mkNeg(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], multiabdVars[*it2])));

                    if (!u.isSat(mknary<FORALL>(args), sol.empty() ? mk<TRUE>(m_efac) : disjoin(negModels, m_efac)))
                    {
                      candidates[r].insert(sol.begin(), sol.end());
                      histRec.push_back(conjoin(sol, m_efac));
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                        allGuesses.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      break;
                    }
                    else
                    {
                      ExprSet models;
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      {
                        ExprSet elements;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          elements.insert(mk<EQ>(ruleManager.invVars[r][i], u.getModel(multiabdVars[*it2][i])));
                        models.insert(conjoin(elements, m_efac));
                      }
                      sol.insert (disjoin(models, m_efac)); // weakening sol by a new model
                    }

                    // heuristic to accelerate convergence
                    ExprVector chk;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      chk.push_back(replaceAll(disjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                    sol.clear();
                    for (auto it1 = occursNum[r].begin(); it1 != occursNum[r].end(); ++it1)
                    {
                      int cnt = 0;
                      for (auto it3 = occursNum[r].begin(); it3 != it1; ++it3, ++cnt)
                        chk[cnt] = replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it3]);
                      chk[cnt] = mk<TRUE>(m_efac);

                      ExprSet allNonlin;
                      allNonlin.insert(mkNeg(b));
                      allNonlin.insert(conjoin(chk, m_efac));
                      preproGuessing(conjoin(allNonlin, m_efac), hr.srcVars[*it1], ruleManager.invVars[r], sol, true, false);
                    }
                    u.removeRedundantConjuncts(sol);
                  }
                }
              }
              processed.insert(r);
            }

            // fairness heuristic (need to be tested properly):
            {
              bool tryAgain = false;
              if (!abdHistory[&hr].empty() && equivVecs(abdHistory[&hr].back(), histRec))
              {
                candidates = candidatesTmp;

                for (int i = 0; i < histRec.size(); i++)
                {
                  if (u.isEquiv(curCnd[i], histRec[i]))
                  {
                    numTrueCands++;
                    trueCands[i] = true;
                    trueRels.insert(rels[i]);
                  }
                  else
                  {
                    trueCands[i] = false;
                    allGuessesInit.insert(curCnd[i]);
                  }
                }
                tryAgain = true; // to keep
              }

              abdHistory[&hr].push_back(histRec);

              if (tryAgain)
              {
                if (abdHistory[&hr].size() > 5 /*hardcoded bound*/)
                {
                  tryAgain = false;
                  for (int i = 0; i < 5 /*hardcoded bound*/; i++)
                    if (abdHistory[&hr][abdHistory[&hr].size() - 1 - i] != histRec)
                    {
                      tryAgain = true;
                      break;
                    }
                }
              }

              if (!tryAgain) ++it;
            }
//            outs () << "sanity check: " << u.implies(conjoin(allGuesses, m_efac), a) << "\n";
          }
        }

    void propagateRangeBackward(HornRuleExt& hr, ExprVector& invVars, ExprVector& srcVars, int i = 0)
    {
      Expr& srcRel = hr.srcRelations[i];
      ExprSet allCands;
      for (auto & c : hr.srcRelations) allCands.insert(candidates[c].begin(), candidates[c].end());
      Expr e = conjoin(allCands, m_efac);
      if (containsOp<FORALL>(e))
      {
        e = u.removeRedundantConjuncts(mk<AND>(e, hr.body));
        if (!containsOp<FORALL>(e))
        {
          vector<HornRuleExt*> worklist;
          worklist.push_back(&hr);
          bool candInd = multiHoudini(worklist, false);  // hope to only call weakenForall
          if (candInd) return;
          else
          {
            if (!checkCHC(hr, candidates))
            {
              Expr model = u.getModel();
              if (isSkippable(model, hr.dstVars)) return;

              ExprSet newCands;
              for (auto it = candidates[srcRel].begin(); it != candidates[srcRel].end(); ++it)
              {
                Expr c = *it;
                if (isOpX<FORALL>(c))
                {
                  ExprSet qVars, range, cellFla, newRange, allSatFla, models, all, newCnd;
                  getQuantifiedVars(c, qVars);
                  getDisj(c->last(), range);
                  Expr repl = mkNeg(replaceAll(c, ruleManager.invVars[srcRel], hr.dstVars));
                  allSatFla.insert(model);
                  allSatFla.insert(repl->last());
                  ExprMap matchVars;
                  while (u.isSat(allSatFla))
                  {
                    Expr nextModel = u.getModel();
                    allSatFla.insert(mkNeg(nextModel));
                    models.insert(nextModel);
                    for (auto & q : qVars)
                      for (auto & s : srcVars)
                        if (u.getModel(q) == u.getModel(s))
                          matchVars[s] = q;
                  }

                  Expr allModels = disjoin(models, m_efac);
                  for (auto & r : range)
                  {
                    if (containsOp<SELECT>(r))
                    {
                      cellFla.insert(r);
                      continue;
                    }
                    if (u.isSat(r, allModels)) newRange.insert (mkNeg(r));
                    else newRange.insert(r);
                  }

                  all.insert(replaceAll(hr.body, matchVars));
                  all.insert(mkNeg(replaceAll(disjoin(cellFla, m_efac), ruleManager.invVars[srcRel], hr.dstVars)));
                  ExprVector srcVarsE = srcVars;
                  srcVarsE.insert(srcVarsE.end(), qVars.begin(), qVars.end());
                  ExprVector invVarsE = invVars;
                  invVarsE.insert(invVarsE.end(), qVars.begin(), qVars.end());
                  preproGuessing(conjoin(all, m_efac), srcVarsE, invVarsE, newCnd, true, false);
                  getDisj(conjoin(newCnd, m_efac), newRange);
                  Expr newCand = replaceAll(c, c->last(), disjoin(newRange, m_efac));
                  newCands.insert(newCand);
                }
              }
              candidates[srcRel].insert(newCands.begin(), newCands.end());
              multiHoudini(worklist, false);  // to double-check
            }
          }
        }
      }
    }

    // inductive strengthening of candidates (by abduction)
    void strengthen(int deep = 0)
    {
      if (deep >= strenBound) return;

      // currently, relies on the order in CHC file; TBD: proper backwards traversing
      for (auto hr = ruleManager.chcs.rbegin(); hr != ruleManager.chcs.rend(); hr++)
      {
        if (!hr->isFact)
        {
          filterUnsat();
          if (!checkCHC(*hr, candidates))
          {
            propagateCandidatesBackward(*hr, deep == strenBound - 1);
            strengthen(deep+1);
          }
        }
      }
    }

    void forceConvergence (ExprSet& prev, ExprSet& next)
    {
      if (prev.size() < 1 || next.size() < 1) return;
      ExprFactory& efac = (*next.begin())->getFactory();

      ExprSet prevSplit, nextSplit, prevSplitDisj, nextSplitDisj, common;

      for (auto & a : prev) getConj (a, prevSplit);
      for (auto & a : next) getConj (a, nextSplit);

      // mergeDiseqs(prevSplit);
      // mergeDiseqs(nextSplit);

      if (prevSplit.size() != 1 || nextSplit.size() != 1)
        return; // GF: to extend

      getDisj(*prevSplit.begin(), prevSplitDisj);
      getDisj(*nextSplit.begin(), nextSplitDisj);

      for (auto & a : prevSplitDisj)
        for (auto & b : nextSplitDisj)
          if (a == b) common.insert(a);

      if (common.empty()) return;
      next.clear();
      next.insert(disjoin(common, efac));
    }

    bool equivVecs (ExprVector e1, ExprVector e2)
    {
      if (e1.size() != e2.size()) return false;
      for (int i = 0; i < e1.size(); i++)
      {
        if (!u.isEquiv(e1[i], e2[i])) return false;
      }
      return true;
    }

    void getImplicationGuesses(map<Expr, ExprSet>& postconds)
    {
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs)
      {
        if (r.isQuery) continue;

        int srcRelInd = -1;
        Expr rel = r.head->left();
        for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == rel) srcRelInd = i;
        if (srcRelInd >= 0)
          preproGuessing(r.body, r.srcVars[srcRelInd], ruleManager.invVars[rel], preconds[rel]);

        if (srcRelInd == -1) continue;
        int tot = 0;
        for (auto guess : postconds[rel])
        {
          if (tot > 5) break; // empirically chosen bound
          if (isOpX<IMPL>(guess) || isOpX<OR>(guess)) continue; // hack

          for (auto & pre : preconds[rel])
          {
            if (u.implies(pre, guess)) continue;
            tot++;
            Expr newGuess = mk<IMPL>(pre, guess);
            ExprVector tmp;
            tmp.push_back(replaceAll(newGuess, ruleManager.invVars[rel], r.srcVars[srcRelInd]));
            tmp.push_back(r.body);
            // simple invariant check (for speed, need to be enhanced)
            if (u.implies (conjoin(tmp, m_efac), replaceAll(newGuess, ruleManager.invVars[rel], r.dstVars)))
            {
              candidates[rel].insert(newGuess);
              ExprSet newPost;
              tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[rel], r.dstVars)));
              preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[rel], newPost);
              for (auto & a : newPost)
                candidates[rel].insert(mk<IMPL>(mk<NEG>(pre), a));
            }
          }
        }
      }
    }

    void printCands(bool unsat = true, bool simplify = false)
    {
      printCands(outs(), unsat, simplify);
    }

    template <typename OutputStream>
    OutputStream & printCands(OutputStream & out, bool unsat = true, bool simplify = false)
    {
      if (unsat) out << "unsat\n";

      for (auto & a : candidates)
      {
        ExprSet lms = a.second;
        Expr sol = conjoin(lms, m_efac);
        
        out << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          out << "(" << *b << " " << u.varType(b) << ")";
        }
        out << ") Bool\n  ";


        // sanity checks:
        ExprSet allVars;
        filter (sol, bind::IsConst (), inserter (allVars, allVars.begin()));
        minusSets(allVars, ruleManager.invVars[a.first]);
        map<Expr, ExprVector> qv;
        getQVars (sol, qv);
        for (auto & q : qv) minusSets(allVars, q.second);
        // assert (allVars.empty());
//        if (!u.isSat(sol)) assert(0);

        Expr res = (simplifyArithm(sol));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        u.print(res, out);
        out << ")\n";
      }
      return out;
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second))
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact) worklist.push_back(&hr);

      multiHoudini(worklist, false);

      for (auto & a : candidates)
      {
        if (!u.isSat(a.second))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          u.splitUnsatSets(a.second, tmp, stub);
          a.second.clear();
          a.second.insert(tmp.begin(), tmp.end());
        }
      }

      return true;
    }

    Expr getQuantifiedCands(bool fwd, HornRuleExt& hr)
    {
      ExprSet qVars;
      Expr body = hr.body;
      if (fwd && hr.isFact)
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())  // immediately try proving properties if already quantified
        {
          // make sure that we can use it as a property (i.e., variables check)

          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          bool allGood = true;
          for (auto & v : allVars)
            if (find (hr.dstVars.begin(), hr.dstVars.end(), v) == hr.dstVars.end())
              { allGood = false; break; }
          if (allGood)
          {
            ExprSet tmpSet;
            getQuantifiedFormulas(hr.body, tmpSet);
            for (auto c : tmpSet)
            {
              // over-approximate the body such that it can pass through the seed mining etc..
              body = replaceAll(body, c, mk<TRUE>(m_efac));
              c = replaceAll(c, hr.dstVars, ruleManager.invVars[hr.dstRelation]);
              candidates[hr.dstRelation].insert(c);
            }
          }
        }
      }
      if (!fwd && hr.isQuery)  // similar for the query
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())
        {
          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            bool toCont = false;
            for (auto & v : allVars)
              if (find (hr.srcVars[i].begin(), hr.srcVars[i].end(), v) == hr.srcVars[i].end())
                { toCont = true; break; }
            if (toCont) continue;
            getQuantifiedFormulas(mkNeg(hr.body), candidates[hr.srcRelations[i]]);
          }
          return NULL; // just as an indicator that everything went well
        }
      }
      return body;
    }

    bool isSkippable(Expr model, ExprVector vars/*, map<Expr, ExprSet>& cands*/)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp)) return true;
      }

//      for (auto & a : cands)
//        for (auto & b : a.second)
//          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    // GF: currently works only for linear (inductive) CHCs, to extend
    Expr strengthenExists(Expr fla, Expr model)
    {
      ExprSet all;
      getDisj(fla, all);
      bool res = false;
      for (auto it = all.begin(); it != all.end(); )
      {
        if (u.isSat(model, *it))
        {
          res = true;
          it = all.erase(it);
        }
        else ++it;
      }
      if (res) return disjoin(all, fla->getFactory());
      return NULL;
    }

    Expr weakenForall(Expr fla, ExprVector& srcVars, ExprVector& dstVars, Expr model)
    {
      ExprSet qfree;
      getDisj(fla->last(), qfree);
      int erased = 0;
      Expr newCand = fla;

      ExprSet lits;
      getLiterals(fla->last(), lits);
      for (auto & l : lits)
      {
        if (!u.isSat(model, replaceAll(l, srcVars, dstVars)) && !containsOp<SELECT>(l)){
          erased++;
          newCand = replaceAll(newCand, l, mk<FALSE>(m_efac));
          // TODO: should be more careful replacement in the case of quantifier alternation
        }
      }
      if (!qfree.empty() && erased != 0) return newCand;
      return NULL;
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      outs () << "multihoudini, size " << worklist.size() << "\n";

      if (!anyProgress(worklist)) return false;
      auto candidatesTmp = candidates;
      bool res1 = true;
      bool res3 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;

        if (checkCHC(*hr, candidatesTmp))
        {
          outs() << "hrb: " << *(hr->body) << "\n";
          printCands(false);
          outs () << "all good\n";
        }
        else
        {
          res3 = false;
          bool res2;
          Expr dstRel = hr->dstRelation;

          ExprVector srcVars;
          for (int i = 0; i < hr->srcVars.size(); i++)
            srcVars.insert(srcVars.end(), hr->srcVars[i].begin(), hr->srcVars[i].end());

          Expr model = u.getModel(hr->dstVars);
          Expr modelSrc = u.getModel(srcVars);
          outs() << "msrc: " << *modelSrc << "\n";
          outs() << "mdst: " << *model << "\n";
          
          if (isSkippable(model, hr->dstVars))//, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
           outs () << "weaken\n";
            Expr newCand = NULL;
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) {
                res2 = false;
                // if (isOpX<FORALL>(repl))
                //   newCand = weakenForall(*it, ruleManager.invVars[dstRel], hr->dstVars, model);
                // else if (containsOp<EXISTS>(repl) && hr->isInductive)
                //   newCand = strengthenExists(*it, modelSrc);
                it = candidatesTmp[dstRel].erase(it);
              }
              else ++it;
            }
            if (newCand != NULL)
              candidatesTmp[dstRel].insert(newCand);
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return res3;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist)
          if (find(hr->srcRelations.begin(), hr->srcRelations.end(), a.first) !=
              hr->srcRelations.end() || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    enum AbdType : unsigned char
      {
       REAL = 0,
       MOCK
      };

    void initShapeAbduction()
    {
      for (auto i = 0; i < ruleManager.chcs.size(); i++) {
        auto & hr = ruleManager.chcs[i];
        if (find(hr.srcRelations.begin(), hr.srcRelations.end(), hr.dstRelation) != hr.srcRelations.end()) {
          auto & itrs = invItrs[make_pair(i,hr.dstRelation)];
          auto & sizeVars = invSizeVars[hr.dstRelation];
          auto & inc  = invItrInc[hr.dstRelation];
          getIterators(hr, itrs, sizeVars, inc);
        }
      }
      return constructPropOrder();
    }


    //Construct the order in which range abduction has to be performed
    //BFS with fail decl as root; priority to chcs having the same relation in src and dst
    void constructPropOrder()
    {
      ExprVector visited;
      deque<int> q;
      for (auto chcNum : ruleManager.incms[ruleManager.failDecl]) {
        q.push_back(chcNum);
      }
      visited.push_back(ruleManager.failDecl);
      while (!q.empty()) {
        int cur = q.front();
        q.pop_front();
        propOrder.push_back(cur);
        for (auto sinv : ruleManager.chcs[cur].srcRelations) {
          if (find(visited.begin(), visited.end(), sinv) != visited.end()) continue;
          vector<int> incms = ruleManager.incms[sinv];
          for (auto incmsItr = incms.begin(); incmsItr != incms.end();) {
            int i = *incmsItr;
            if (find(ruleManager.chcs[i].srcRelations.begin(),
                     ruleManager.chcs[i].srcRelations.end(),
                     sinv) != ruleManager.chcs[i].srcRelations.end()) {
              q.push_back(i);
              incmsItr = incms.erase(incmsItr);
            } else {
              ++incmsItr;
            }
          }
          for (auto i : incms) {
            q.push_back(i);
          }
          visited.push_back(sinv);
        }
      }
    }

    Expr getPostCondn()
    {
      auto & hr = ruleManager.chcs[ruleManager.qCHCNum];
      ExprSet cnjs;
      getConj(hr.body, cnjs);
      for (auto c : cnjs) {
        if (!isOpX<FORALL>(c) && !isOpX<EXISTS>(c)) continue;
        return c;
      }
      return nullptr;              
    }

    //Simple initial candidate: formula present in the query
    void getQueryArrayCandidates(ExprSet & cands, Expr trel = nullptr, bool negate = true)
    {
      auto & hr = ruleManager.chcs[ruleManager.qCHCNum];
      assert(hr.srcRelations.size() == 1 &&
             "Nonlinear CHCs are not supported");
      //hr.body can have fail; following check avoids adding fail
      ExprSet cnjs;
      getConj(hr.body, cnjs);
          
      ExprSet itrVars;
      for (auto i = 0; i < ruleManager.chcs.size(); i++) {
        copy(invItrs[make_pair(i,hr.srcRelations[0])].begin(),
             invItrs[make_pair(i,hr.srcRelations[0])].end(),
             inserter(itrVars, itrVars.end()));
      }

      for (auto c : cnjs) {
        // assert((isOpX<FORALL>(c) || isOpX<EXISTS>(c)) && "unsupported query body");
        if (!isOpX<FORALL>(c) && !isOpX<EXISTS>(c)) continue;
        ExprVector args;
        for (int i = 0; i < c->arity() - 1; i++) {
          args.push_back(c->arg(i));
        }
            
        ExprSet body;
        if (isOpX<FORALL>(c)) {
          getDisj(c->last(), body);
        } else {
          getConj(c->last(), body);
        }
            
        ExprSet prop;
        ExprSet prange;
        for (auto b : body) {
          if (emptyIntersect(b, itrVars)) {
            prop.insert(b);
            if (!containsOp<ARRAY_TY>(b)) {
              prange.insert(b);
            }
          }
        }

        // if (isOpX<EXISTS>(c) && negate) {
        //   ExprSet qvars;
        //   getQuantifiedVars(c, qvars);            
        //   bool itrUp = invItrInc[hr.srcRelations[0]];
        //   for (auto qvar : qvars) {
        //     for (auto ivar : itrVars) {
        //       Expr newCondn = itrUp ? mk<LT>(qvar, ivar) : mk<GT>(qvar, ivar);
        //       prop.insert(newCondn);
        //       prange.insert(mkNeg(newCondn));
        //     }
        //   }
        // }

        ExprSet qvars;
        getQuantifiedVars(c, qvars);            
        bool itrUp = invItrInc[hr.srcRelations[0]];
        for (auto qvar : qvars) {
          for (auto ivar : itrVars) {
            Expr newCondn = itrUp ? mk<LT>(qvar, ivar) : mk<GT>(qvar, ivar);
            if (isOpX<EXISTS>(c)) {
              prop.insert(newCondn);
            } else {
              prop.insert(mkNeg(newCondn));
              prange.insert(newCondn);
            }
          }
        }

        Expr cand;
        if (isOpX<FORALL>(c)) {
          ExprVector args2(args);
          args.push_back(disjoin(prop, m_efac));
          args2.push_back(disjoin(prange, m_efac));
          cand = mk<AND>(mknary<FORALL>(args), mknary<FORALL>(args2));
        } else {
          args.push_back(conjoin(prop, m_efac));
          cand = mknary<EXISTS>(args);
        }
        cand = negate ? mkNeg(cand) : cand;
        cand = replaceAll(cand, hr.srcVars[0], trel == nullptr ? ruleManager.invVars[hr.srcRelations[0]] : ruleManager.invVars[trel]);
        cands.insert(cand);
      }
          
      // ExprSet cand;
      // ExprVector allVars = hr.locVars;
      // for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());          
      // for (auto & a : cnjs)
      // {
      //   outs() << "a: " << *a << "\n";
      //   if (!emptyIntersect(a, allVars)) {
      //     cand.insert(mkNeg(a));
      //   }
      // }
      // Expr c = disjoin(cand, m_efac);
      // c = replaceAll(c, hr.srcVars[0], ruleManager.invVars[hr.srcRelations[0]]);
      // candidates[hr.srcRelations[0]].insert(c);
      return;
    }

    void getIterators(HornRuleExt& hr, ExprVector& itrs, ExprVector & sizeVars, bool & incr)
    {
      for (int i = 0; i < hr.srcVars[0].size(); i++) {
        Expr sv = hr.srcVars[0][i];
        Expr dv = hr.dstVars[i];
        if (containsOp<ARRAY_TY>(sv) || containsOp<ARRAY_TY>(dv)) continue;
        if (u.implies(hr.body, mk<GT>(sv,dv))) {
          incr = false;
          itrs.push_back(sv);
        } else if (u.implies(hr.body, mk<LT>(sv,dv))) {
          incr = true;
          itrs.push_back(sv);
        } else if (u.implies(hr.body, mk<EQ>(sv,dv))) {
          sizeVars.push_back(sv);
        }
      }
    }


    Expr getMockArrayAssign(HornRuleExt& hr, const ExprVector & qVars)
    {
      ExprSet dassign;
      for (int i = 0; i < hr.srcVars[0].size(); i++) {
        if (containsOp<ARRAY_TY>(hr.srcVars[0][i])) {
          for (auto qv : qVars) {
            dassign.insert(mk<EQ>(hr.dstVars[i],
                                  mk<STORE>(hr.srcVars[0][i],
                                            qv,
                                            mk<SELECT>(hr.srcVars[0][i], qv))));
          }
        } else if (!containsOp<ARRAY_TY>(hr.dstVars[i])) {
          dassign.insert(mk<EQ>(hr.dstVars[i], hr.srcVars[0][i]));
        }
      }
      outs () << "   mock:  ";
      pprint(dassign, 3);
      return conjoin(dassign, m_efac);
    }

    Expr getMockArrayAssignNew(Expr nbt, const ExprVector & qVars)
    {
      // GF: hack for now; to extend
      ExprSet returnCnj;
      if (isOpX<EQ>(nbt))
      {
        Expr srcVar = NULL, dstVar = NULL;
        if (isOpX<FAPP>(nbt->left()))
          srcVar = nbt->left();
        if (isOpX<FAPP>(nbt->right()))
          dstVar = nbt->right();
        if (isOpX<STORE>(nbt->left()) && isOpX<FAPP>(nbt->left()->left()))
          srcVar = nbt->left()->left();
        if (isOpX<STORE>(nbt->right()) && isOpX<FAPP>(nbt->right()->left()))
          dstVar = nbt->right()->left();
        // TODO: extend for the case of nested STORE-s
        if (srcVar != NULL && dstVar != NULL)
          for (auto & q : qVars)
            returnCnj.insert(mk<EQ>(mk<SELECT>(srcVar, q),
                                 mk<SELECT>(dstVar, q)));
        else assert(0 && "not implemented");
      }

      return conjoin(returnCnj, m_efac);
    }

    Expr getArrayFormula(HornRuleExt& hr, Expr dc, AbdType abd, ExprVector qVars, ExprVector itrVars, Expr nondetGuard = nullptr)
    {
      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      ExprVector srcVars(hr.srcVars[0].begin(), hr.srcVars[0].end());
      ExprVector dstVars(hr.dstVars.begin(), hr.dstVars.end());
      ExprVector srcInvVars(ruleManager.invVars[srcRel].begin(), ruleManager.invVars[srcRel].end());
      ExprVector dstInvVars(ruleManager.invVars[dstRel].begin(), ruleManager.invVars[dstRel].end());

      ExprVector vars2keep, prjcts, cellFls, res;
      Expr newBody = hr.body;
      if (nondetGuard != nullptr) {
        newBody = mk<AND>(newBody, nondetGuard);
      }
      u.flatten(newBody, prjcts, false, vars2keep, [](Expr a, ExprVector& b){return a;});
      for (auto b : prjcts)
      {
        ExprVector all = {mkNeg(replaceAll(dc, dstInvVars, dstVars))};
        outs () << "dc: " << all.back() << "\n";
        ExprSet nbodyTmp;
        getConj(b, nbodyTmp);
        for (auto nbt : nbodyTmp)
        {
          outs () << "    >>> nbt " << nbt << "\n";
          if (containsOp<ARRAY_TY>(nbt)) {
            if (abd == AbdType::REAL) {
              if (containsOp<STORE>(nbt))
              {
                nbt = replaceAll(nbt, itrVars, qVars);
                nbt = rewriteSelectStore(nbt);
              }
              all.push_back(nbt);
            }
            else
            {
              if (isOpX<EQ>(nbt) && isOpX<ARRAY_TY>(typeOf(nbt->left())))
              {
                Expr srcVar = NULL, dstVar = NULL;
                if (isOpX<FAPP>(nbt->left()))
                  srcVar = nbt->left();
                if (isOpX<FAPP>(nbt->right()))
                  dstVar = nbt->right();
                if (isOpX<STORE>(nbt->left()) && isOpX<FAPP>(nbt->left()->left()))
                  srcVar = nbt->left()->left();
                if (isOpX<STORE>(nbt->right()) && isOpX<FAPP>(nbt->right()->left()))
                  dstVar = nbt->right()->left();
                if (isOpX<STORE>(nbt->left()) && isOpX<STORE>(nbt->left()->left()) && isOpX<FAPP>(nbt->left()->left()->left()))
                  srcVar = nbt->left()->left()->left();
                if (isOpX<STORE>(nbt->right()) && isOpX<STORE>(nbt->right()->left()) && isOpX<FAPP>(nbt->right()->left()->left()))
                  dstVar = nbt->right()->left()->left();
                // TODO: extend for the case of nested STORE-s
                if (srcVar != NULL && dstVar != NULL) {
                  // for (auto & q : qVars)
                  //   all.push_back(mk<EQ>(mk<SELECT>(srcVar, q),
                  //                        mk<SELECT>(dstVar, q)));
                  ExprSet inds;
                  getArrInds(all[0], inds);
                  for (auto ind : inds) {
                    ExprSet indVars;
                    filter(ind, bind::IsConst(), inserter(indVars, indVars.begin()));
                    ExprSet dstVarsSet(dstVars.begin(), dstVars.end());
                    if (emptyIntersect(indVars, dstVarsSet)) {
                      all.push_back(mk<EQ>(mk<SELECT>(srcVar, ind),
                                           mk<SELECT>(dstVar, ind)));
                    } else {
                      assert(dstVars.size() == srcVars.size() && "Unsupport mock abduction");
                      Expr indSrc = replaceAll(ind, dstVars, srcVars);
                      all.push_back(mk<EQ>(mk<SELECT>(srcVar, indSrc),
                                           mk<SELECT>(dstVar, ind)));                      
                    }
                  }
                }
                else assert(0 && "not implemented");
              }
              else all.push_back(nbt);
            }
          }         
          else {
            //hack
            if (!emptyIntersect(nbt,hr.locVars)) {
              nbt = replaceAll(nbt, itrVars, qVars);
              all.push_back(nbt);
            } else if (emptyIntersect(nbt, itrVars)) {
              all.push_back(nbt);
            }
          }
          outs () << "      ----> " << all.back() << "\n";
        }
        ExprVector abdVars(qVars.begin(), qVars.end());
        for (auto sv : srcVars) {
          if (find(itrVars.begin(), itrVars.end(), sv) == itrVars.end()) {
            abdVars.push_back(sv);
          }
        }

        // for (auto v : abdVars) {
        //   outs() << "v: " << *v << "\n";
        // }
        // for (auto a : all) {
        //   outs() << "a: " << *a << "\n";
        // }
        
        Expr newCnd = keepQuantifiersRepl(conjoin(all, m_efac), abdVars);

        Expr candres = mkNeg(newCnd);
        ExprSet candresDisj;
        ExprSet candresDisjNonVac;
        getDisj(candres, candresDisj);
        for (auto cd : candresDisj) {
          if (u.isSat(cd, newBody)) {
            candresDisjNonVac.insert(cd);
          }
        }
        
        res.push_back(disjoin(candresDisjNonVac, m_efac));

        outs() << "newcnd: " << *newCnd << "\n" << "abdtype: " << abd << "\n" << "nonvac: " << *(res.back()) << "\n";

        
        
        ExprSet dsjs;   // GF: to improve the identification of cell properties
        getDisj(res.back(), dsjs);    // maybe outside of this procedure
        for (auto & a : dsjs) {
          if (containsOp<SELECT>(a)) {
            cellFls.push_back(a);
          } 
        }
        
      }

      if (false == u.isSat(cellFls))
        return mk<FALSE>(m_efac);
      //preproGuessing(conjoin(all, m_efac), abdVars, abdVars, newCnd, true, false);
      return replaceAll(conjoin(res, m_efac), srcVars, srcInvVars);
    }

    void getRangeFormulas(const ExprVector & qVars, const ExprVector & itrVars, ExprVector & sizeVars, ExprVector & rangeFormulas, bool incr)
    {
      for (auto qv : qVars) {
        for (auto iv : itrVars) {
          if (incr) {
            rangeFormulas.push_back(mk<GEQ>(qv,iv));
          } else {
            rangeFormulas.push_back(mk<LEQ>(qv,iv));
          }
        }
        // for (auto sv : sizeVars) {
        //   if (incr) {
        //     rangeFormulas.push_back(mk<GEQ>(qv,sv));
        //   } else {
        //     rangeFormulas.push_back(mk<LEQ>(qv,sv));
        //   }
        // }
      }
    }

    
    void abduce(const int hrIndex, bool strengthenExists = false)
    {
      auto & hr = ruleManager.chcs[hrIndex];
      
      if (hr.isFact) return;

      if (hr.isQuery) {
        getQueryArrayCandidates(candidates[hr.srcRelations[0]]);
        return;
      }

      assert(hr.srcRelations.size() == 1 &&
             "Nonlinear CHCs are not supported");

      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      ExprSet dstCands;
      for (auto c : candidates[dstRel]) {
        dstCands.insert(simplifyBool(simplifyArithm(c)));
      }

      ExprSet candidatesTmp;
      for (auto c : candidates[srcRel]) {
        candidatesTmp.insert(c);
      }
      
      boost::tribool forall(boost::indeterminate);
      
      for (auto dc : dstCands) {
        ExprSet dcDisjs;
        getDisj(dc, dcDisjs);

        for (auto dcd : dcDisjs) {
          if (isOpX<FORALL>(dcd)) {
            forall = true;
          } else if (isOpX<EXISTS>(dcd)) {
            forall = false;
          } else {
            //TODO: handle non quantified case
            continue;
          }

          outs () << ">>>>>>>>>>>>>> next cand: "<< dcd<<"\n";

          ExprSet qVarsTmp;
          getQuantifiedVars(dcd, qVarsTmp);
          ExprVector qVars(qVarsTmp.begin(), qVarsTmp.end());
          ExprVector & itrVars = invItrs[make_pair(hrIndex, srcRel)];
          ExprVector & sizeVars = invSizeVars[srcRel];
          bool itrUp = invItrInc[srcRel];

          ExprVector arrayFormulas;
          arrayFormulas.push_back(getArrayFormula(hr, dcd->last(), AbdType::REAL, qVars, itrVars));

          if (isOpX<FALSE>(arrayFormulas[0]))
          {
            outs () << "vacuous\n"; // GF: to test better
            // exit(0);
            continue;
          }
          

          //when srcRel is a precondition
          if (itrVars.size() == 0) {
            arrayFormulas.push_back(getArrayFormula(hr, dcd->last(), AbdType::MOCK, qVars, itrVars));
            if (isOpX<FALSE>(arrayFormulas[1])) {
              outs () << "vacuous\n";
              continue;
            }              

            for (auto qv : qVars) {
              ExprVector args1 = {qv->left()};
              if (forall == true)
              {
                args1.push_back(arrayFormulas[1]);
                if (containsOp<ARRAY_TY>(arrayFormulas[1])) {
                  candidatesTmp.insert(mknary<FORALL>(args1));
                } 
              } else if (forall == false)
              {
                args1.push_back(arrayFormulas[1]);
                if (containsOp<ARRAY_TY>(arrayFormulas[1])) {
                  candidatesTmp.insert(mknary<EXISTS>(args1));              
                } 
              }
            }
          }
          
          for (auto qv : qVars) {
            for (auto iv : itrVars) {
              Expr rf;
              if (itrUp) {
                rf = mk<GEQ>(qv,iv);
              } else {
                rf = mk<LEQ>(qv,iv);
              }

              Expr extraCondn = mk<TRUE>(m_efac);
              if (hr.isInductive) {
                ExprSet extraCondns;
                ExprSet bodyConj;
                getConj(hr.body, bodyConj);
                for (auto bc : bodyConj) {
                  if (!emptyIntersect(bc, itrVars) && !isOpX<EQ>(bc)) {
                    extraCondns.insert(replaceAll(bc, itrVars, qVars));
                  }
                }
                extraCondn = conjoin(extraCondns, m_efac);
              }
              
              outs() << "RF: " << *rf << "\n";
              outs() << "AF0: " << *(arrayFormulas[0]) << "\n";
              
              ExprVector args1 = {qv->left()};
              ExprVector args2 = args1;
              if (forall == true)
              {
                if (hr.isInductive)
                {
                  extraCondn = mkNeg(extraCondn);
                  args1.push_back(mk<OR>(arrayFormulas[0], mk<NEG>(rf), extraCondn));
                  if (containsOp<ARRAY_TY>(arrayFormulas[0]))
                    candidatesTmp.insert(mknary<FORALL>(args1));
                }
                else
                {
                  args1.push_back(arrayFormulas[0]);
                  if (containsOp<ARRAY_TY>(arrayFormulas[0])) {
                    candidatesTmp.insert(mknary<FORALL>(args1));
                  }
                }
              } else if (forall == false) {
                if (hr.isInductive)
                {
                  args1.push_back(mk<AND>(arrayFormulas[0], rf, extraCondn));
                  candidatesTmp.insert(mknary<EXISTS>(args1));
                }
                else
                {
                  bool cp1 = containsOp<ARRAY_TY>(arrayFormulas[0]);
                  args1.push_back(arrayFormulas[0]);
                  if (cp1)
                    candidatesTmp.insert(mknary<EXISTS>(args1));
                }
              }
            }
          }
        }
      }

      candidates[srcRel].clear();
      if (forall == true) {
        for (auto c : candidatesTmp) {
          candidates[srcRel].insert(c);
        }
      } else {
        ExprSet cdisj;
        for (auto c : candidatesTmp) {
          ExprSet cd;
          getDisj(c, cd);
          for (auto cdItr = cd.begin(); cdItr != cd.end();) {
            if (!containsOp<ARRAY_TY>(*cdItr)) {
              cdItr = cd.erase(cdItr);
            } else {
              ++cdItr;
            }
          }
          cdisj.insert(disjoin(cd, m_efac));
        }
        candidates[srcRel].insert(disjoin(cdisj, m_efac));
      }
    }

    
    void newWeaken(int hrIndex)
    {
      auto & hr = ruleManager.chcs[hrIndex];
      if (hr.isFact) return;

      if (hr.isQuery) {
        getQueryArrayCandidates(candidates[hr.srcRelations[0]]);
        return;
      }

      assert(hr.srcRelations.size() == 1 &&
             "Nonlinear CHCs are not supported");

      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];

      outs () << " - - newWeaken - - " <<  srcRel << " -> " << dstRel << "\n";
      ExprSet dstCands;
      for (auto c : candidates[dstRel]) {
        dstCands.insert(simplifyBool(simplifyArithm(c)));
      }

      for (auto dcd : dstCands) {
        boost::tribool forall(boost::indeterminate);
        if (isOpX<FORALL>(dcd)) {
          forall = true;
        } else if (isOpX<EXISTS>(dcd)) {
          forall = false;
        } else {
          //TODO: handle non quantified case
          continue;
        }

        outs () << ">>>>>>>>>>>>>> next cand: "<< dcd <<"\n";

        ExprSet qVarsTmp;
        getQuantifiedVars(dcd, qVarsTmp);

        for (auto qv : qVarsTmp) {

          for (auto iv : invItrs[make_pair(hrIndex,srcRel)]) {
            Expr rf;
            if (invItrInc[srcRel]) {
              rf = mk<GEQ>(qv,iv);
            } else {
              rf = mk<LEQ>(qv,iv);
            }

            outs() << "RF: " << *rf << "\n";

            auto candidatesTmp = candidates;
            if (forall == true)
            {
              dcd = replaceAll(dcd, dcd->last(), mk<OR>(rf, dcd->last()));
            } else if (forall == false) {
              dcd = replaceAll(dcd, dcd->last(), mk<AND>(rf, dcd->last()));
            }

            if (u.isFalse(dcd)) {
              continue;
            }
            
            candidatesTmp[srcRel].insert(dcd);
            if (checkCHC(hr, candidatesTmp)) {
              candidates[srcRel].insert(dcd);
            }
          }
        }
      }
    }

    //Backward propagation from query
    Result_t inferInv()
    {
      for (int i = 0; i < propOrder.size(); i++) {
        int hrIndex = propOrder[i];
        auto & hr = ruleManager.chcs[hrIndex];
        outs () << "\n\n\n===============\ninferInv for chc:  " <<
          (hr.srcRelations.empty() ? "" : lexical_cast<string>(hr.srcRelations[0]))
                << " -> " << hr.dstRelation << "\n";

        outs() << "\n\n hr.body " << *(hr.body) <<  "\n\n";
        auto candidatesTmp = candidates;
        if (!hr.srcRelations.empty())
        {
          outs () << "cands [src]:  \n";
          pprint(candidates[hr.srcRelations[0]], 2);
          if (hr.srcRelations[0] != hr.dstRelation)
          {
            outs () << "cands [dst]:  \n";
            pprint(candidates[hr.dstRelation], 2);
          }
        }

        bool res = checkCHC(hr, candidates, true);
        if (!res) {
          abduce(hrIndex);
          outs() << "\n src->";
          pprint(candidates[hr.srcRelations[0]], 2);
          outs() << "\n dst->";
          pprint(candidates[hr.dstRelation], 2);
          
          //no progress
          if (equalCands(candidatesTmp)) {
            break;
          }
        }
      }

      // double check
      filterUnsat();
      if (checkAllOver(true)) {
        printCands();
        return Result_t::UNSAT;
      } else {
        outs () << "unknown\n";
        return Result_t::UNKNOWN;
      }
    }

    ExprVector getAllRels()
    {
      ExprVector retRels;

      for (auto d : ruleManager.decls) {
        retRels.push_back(d->left());
      }

      return retRels;
    }



    void sanitizeForDump(string & in)
    {
      in.erase(remove(in.begin(), in.end(), '_'), in.end());
      in.erase(remove(in.begin(), in.end(), '|'), in.end());

      map<char,char> substmap;
      // substmap['_'] = 'U';
      // substmap['|'] = 'B';
      substmap['\''] = 'P';
      substmap['$'] = 'D';
      substmap[':'] = 'C';
      substmap[';'] = 'c';

      for (size_t i = 0; i < in.size(); i++) {
        auto subst = substmap.find(in[i]);
        if (subst != substmap.end()) {
          in[i] = subst->second;
        }
      }
      // std::replace(in.begin(), in.end(), '\'', 'p');
      // std::replace(in.begin(), in.end(), '$', 'D');
      // std::replace(in.begin(), in.end(), ':', 'C');
    }

    string typeToString(Expr ty)
    {
      if (isOpX<BOOL_TY>(ty)) return string("Bool ");
      else if (isOpX<REAL_TY>(ty)) return string("Real ");
      else if (isOpX<INT_TY>(ty)) return string("Int ");
      else if (isOpX<ARRAY_TY>(ty)) return string("(Array ") +
                                      typeToString(ty->left()) +
                                      string(" ") +
                                      typeToString(ty->right()) +
                                      string(") ");
      else return string("UnSupportedSort ");
    }
    
    
    void printAllVarsRels(const ExprSet & allVars, stringstream & decls)
    {
      for (auto v : allVars) {
        decls << "(declare-var " << *v << " " << u.varType(v) << ")\n";
      }

      for (auto d : ruleManager.decls) {
        if (d == ruleManager.failDecl) continue;
        decls << "(declare-rel " << *bind::fname(d) << " (";
        for (unsigned i = 0; i < bind::domainSz(d); i++)
        {
          Expr ty = bind::domainTy(d, i);
          decls << typeToString(ty);
        }
        decls << ")) \n";
      }
    }

    string dumpToFile(stringstream & decls, stringstream & rules, string oldsmt = "", string postfix = "")
    {
      if (oldsmt.size() == 0) {
        oldsmt = ruleManager.infile;
      }

      string newsmt = oldsmt.substr(oldsmt.find_last_of("/"));
      newsmt = "/tmp/" + newsmt.substr(0, newsmt.find_last_of("."));
      newsmt += postfix + "_" + to_string(std::chrono::system_clock::now().time_since_epoch().count());
      newsmt += ".smt2";

      string ds = decls.str();
      string rs = rules.str();

      sanitizeForDump(ds);
      sanitizeForDump(rs);

      ofstream newsmtFile(newsmt);      
      newsmtFile << ds << "\n" << rs << "\n";
      newsmtFile.close();

      return newsmt;
    }
    
    //construct a new sytem of CHCs with the same structure of
    //current system except:
    //when precondn is given add precondn -> inv instead of existing fact
    string constructRules(const Expr & curPost, const Expr & loopCondn, Expr precondn = nullptr, bool negProp = true, string filenamesuffix = "")
    {
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = isOpX<FALSE>(ruleManager.failDecl) ? "fail" : lexical_cast<string>(ruleManager.failDecl);

      for (auto inve : ruleManager.invVars) {
        allVars.insert(inve.second.begin(), inve.second.end());
      }

      Expr pRel = getPrecondnRel();
      int pChcIndex = getPrecondnCHC(pRel);

      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & hr = ruleManager.chcs[i];
        
        bool precondnRule = (i == pChcIndex && precondn != nullptr);
        
        for (int i = 0; i < hr.srcVars.size(); i++) {
          allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
        }
        allVars.insert(hr.locVars.begin(), hr.locVars.end());
        allVars.insert(hr.dstVars.begin(), hr.dstVars.end());

        ExprSet antec;
        if (!precondnRule) {
          for (int i = 0; i < hr.srcRelations.size(); i++) {
            Expr src = hr.srcRelations[i];
            for (auto d : ruleManager.decls) {
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
                Expr t = bind::fapp(d, hr.srcVars[i]);
                antec.insert(t);
                break;
              }
            }
          }
        }

        bool addFail;
        Expr conseq;
        if (!hr.isQuery) {
          addFail = false;
          antec.insert(precondnRule ? mk<AND>(hr.body, precondn) : hr.body);
          for (auto d : ruleManager.decls) {
            if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
              conseq = bind::fapp(d, hr.dstVars);
              break;
            }
          }
        } else {
          antec.insert(negProp ? mkNeg(curPost) : curPost );
          antec.insert(loopCondn);
          addFail = true;
        }
        
        if (addFail) {
          newRules << "(rule (=> ";
          u.print(conjoin(antec, m_efac), newRules);
          newRules << " " << queryRelStr << "))\n";
        } else {
          newRules << "(rule ";
          u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
          newRules << ")\n";
        }
      }
      
      printAllVarsRels(allVars, newDecls);
      newDecls << "(declare-rel " << queryRelStr << "())\n";
      newRules << "(query " << queryRelStr << ")\n";
      return dumpToFile(newDecls, newRules, ruleManager.infile, filenamesuffix);
    }

    Expr getPrecondnRel()
    {
      ExprVector allRels = getAllRels();
      for (auto aItr = allRels.begin(); aItr != allRels.end();)
      {
        bool notPRel = false;
        for (auto & hr : ruleManager.chcs) {
          if (*aItr == hr.dstRelation) {
            if (hr.isFact ||
                hr.isInductive &&
                find(hr.srcRelations.begin(), hr.srcRelations.end(), hr.dstRelation) != hr.srcRelations.end()) {
              notPRel = true;
            }
          } else if(hr.isQuery &&
                    find(hr.srcRelations.begin(), hr.srcRelations.end(), hr.dstRelation) != hr.srcRelations.end()) {
            notPRel = true;
          }
        }        
        if (notPRel) {
          aItr = allRels.erase(aItr);
        } else {
          ++aItr;
        }            
      }      
      // assert(allRels.size() == 1 &&
      //        "number of preconditions should be one");
      return allRels.size() == 0 ? nullptr : allRels[0];
    }

    int getPrecondnCHC(const Expr & pcRel)
    {
      for (int i=0; i < ruleManager.chcs.size(); i++)
      {
        auto & hr = ruleManager.chcs[i];
        if (hr.srcRelations[0] == pcRel) {
          return i;
        }
      }
      return -1;
    }
  
    // void splitPrecond(const Expr & pcRel, vector<boost::tribool> & foralls, vector<ExprSet> & qVarss, ExprVector & rfs, ExprVector & afs)
    // {
    //   for (auto pc : candidates[pcRel]) {
    //     if (isOpX<FORALL>(pc)) {
    //       foralls.push_back(true);
    //     } else if (isOpX<EXISTS>(pc)) {
    //       foralls.push_back(false);
    //     } else {
    //       foralls.push_back(boost::indeterminate);
    //     }

    //     ExprSet pcqVars;
    //     getQuantifiedVars(pc, pcqVars);
    //     qVarss.push_back(pcqVars);
        
    //     ExprSet disjs;
    //     ExprSet pcafs;
    //     ExprSet pcrfs;        
    //     getDisj(pc, disjs);
    //     for (auto pcd : disjs) {
    //       if (containsOp<ARRAY_TY>(pcd)) {
    //         pcafs.insert(pcd);
    //       } else {
    //         pcrfs.insert(mkNeg(pcd));
    //       }
    //     }
    //     rfs.push_back(conjoin(pcrfs));
    //     afs.push_back(conjoin(pcafs));
    //   }      
    // }

    void splitQueryBody(Expr & post, Expr & loopCondn)
    {
      HornRuleExt& hr = ruleManager.chcs[ruleManager.qCHCNum];
      ExprSet cnjs;
      ExprSet termCondns;
      ExprSet newCnjs;
      if (isOpX<EXISTS>(hr.body)) {
        getConj((hr.body)->last(), cnjs);
      } else {
        getConj(hr.body, cnjs);
      }
      ExprVector allVars;
      for (auto  vars : hr.srcVars) allVars.insert(allVars.end(), vars.begin(), vars.end());
      for (auto  c : cnjs)
      {
        if (!isSubset(c, allVars)) newCnjs.insert(c);
        else termCondns.insert(c);
      }
      if (isOpX<EXISTS>(hr.body)) {
        ExprSet qVars;
        getQuantifiedVars(hr.body, qVars);
        ExprVector args(qVars.begin(), qVars.end());
        args.push_back(conjoin(newCnjs, m_efac));
        post = mknary<EXISTS>(args);
      } else {
        post =conjoin(newCnjs, m_efac);
      }
      
      loopCondn = conjoin(termCondns, m_efac);
    }

    void getSoln(map<Expr, ExprSet> & soln, const ExprVector & rels, map<Expr, ExprVector> & invVars)
    {
      for (auto r : rels) {
        soln[r].clear();
        for (auto e : candidates) {
          string saneName = lexical_cast<string>(*r);
          sanitizeForDump(saneName);
          if (saneName == lexical_cast<string>(*(e.first))) {
            for (auto c : e.second) {
              soln[r].insert(replaceAll(c, ruleManager.invVars[e.first], invVars[r]));
            }
          }
        }
      }
    }

        
    Result_t solveInverse(const string & invsmt, map<Expr, ExprSet> & soln)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(invsmt);
      NonlinCHCsolver newNonlin(nrm, 1);
      ExprVector query;

      newNonlin.initShapeAbduction();
      Result_t res = newNonlin.inferInv();
      assert(res != Result_t::SAT);

      if (res == Result_t::UNSAT) {
        ExprVector allRels = getAllRels();
        newNonlin.getSoln(soln, allRels, ruleManager.invVars);
      }

      return res;
    }

    bool pWeakCheck(map<Expr, ExprSet> & invSoln, Expr & ctm)
    {
      // Expr pRel = getPrecondnRel();
      // int chcIndex = getPrecondnCHC(pRel);
      // assert (chcIndex >= 0);
      // auto pCHC = ruleManager.chcs[chcIndex];
      // Expr dstRel = pCHC.dstRelation;

      // map<Expr, ExprSet> newCand;
      // newCand[dstRel].insert(invSoln[dstRel].begin(), invSoln[dstRel].end());
      // newCand[pRel].insert(mkNeg(conjoin(candidates[pRel], m_efac)));
      
      // return checkCHC(pCHC, newCand);

      Expr pRel = getPrecondnRel();
      int chcIndex = getPrecondnCHC(pRel);
      assert (chcIndex >= 0);
      HornRuleExt& pCHC = ruleManager.chcs[chcIndex];
      Expr pBody = pCHC.body;

      Expr pre = conjoin(candidates[pRel], m_efac);
      Expr cpre = conjoin(invSoln[pRel], m_efac);
      if (u.isSat(mkNeg(pre), mkNeg(cpre), pBody)) {
        ctm = u.getModel();
        outs() << "!pre: " << *(mkNeg(pre)) << "\n";
        outs() << "!cpre: " << *(mkNeg(cpre)) << "\n";
        outs() << "ctm: " << *ctm << "\n";
        return false;
      } else {
        return true;
      }
          //return bool(!u.isSat(mk<NEG>(pre), mk<NEG>(cpre)));
    }

    //return true if reaches property, otherwise false
    Result_t executeChc(Expr & ctm, bool invProp)
    {
      Expr post;
      Expr loopCondn;
      splitQueryBody(post, loopCondn);      
      string newChcFile = constructRules(post, loopCondn, ctm, invProp);      
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newChcFile);
      NonlinCHCsolver newNonlin(nrm, 1);
      
      switch(newNonlin.solveIncrementally(10)) {
      case 0: return Result_t::SAT;
      case 1: return Result_t::UNSAT;
      default: return Result_t::UNKNOWN;
      }
      
    }

    //A simple sygus based candidate synthesis
    Expr sygusWeaken(Expr ctm, bool prectm)
    {
      Expr res = mk<TRUE>(m_efac);
      ExprSet intExpr;
      ExprSet arrExpr;
      Expr pRel = getPrecondnRel();
      int pChcIndex = getPrecondnCHC(pRel);
      HornRuleExt& pCHC = ruleManager.chcs[pChcIndex];
      HornRuleExt& qCHC = ruleManager.chcs[ruleManager.qCHCNum];
                            
      ctm = replaceAll(ctm, qCHC.srcVars[0], ruleManager.invVars[pRel]);
      
      getQueryArrayCandidates(arrExpr, pRel, prectm);
      
      for (auto a : arrExpr) {
        for (int i = 0; i < ruleManager.chcs.size(); i++) {
          auto & hr = ruleManager.chcs[i];          
          if (hr.isInductive) {
            ExprSet qVarsTmp;
            getQuantifiedVars(a, qVarsTmp);
            ExprVector qVars(qVarsTmp.begin(), qVarsTmp.end());
            ExprVector itrVars = invItrs[make_pair(i, hr.srcRelations[0])];
            ExprSet extraCondns;
            ExprSet bodyConj;
            getConj(hr.body, bodyConj);
            for (auto bc : bodyConj) {
              if (!emptyIntersect(bc, itrVars) && !isOpX<EQ>(bc)) {
                extraCondns.insert(replaceAll(bc, itrVars, qVars));
              }
            }
            Expr extraCondn = conjoin(extraCondns, m_efac);
            intExpr.insert(replaceAll(extraCondn, hr.srcVars[0], ruleManager.invVars[pRel]));
          }
        }

        for (auto ie : intExpr) {                    
          ExprVector args;
          for (int j = 0; j < a->arity() - 1; j++) {
            args.push_back(a->arg(j));
          }
          args.push_back(isOpX<EXISTS>(a) ? mk<AND>(a->last(), ie) : mk<OR>(a->last(), ie));
          res = isOpX<EXISTS>(a) ? mknary<EXISTS>(args) : mknary<FORALL>(args);

          // outs() << *res  << endl;
                    
          if (!u.isSat(ctm, mkNeg(res))) {
            return res;
          } else {
            res = mk<TRUE>(m_efac);
          }
        }          
      }
      
      return res;      
    }

    //lightweight invariant finder from precondition
    Result_t solveWithPreHelper()
    {
      ExprVector preconds;
      Expr invRel = nullptr;
      for (auto & hr : ruleManager.chcs) {
        if (!hr.isFact) continue;
        invRel = hr.dstRelation;
        ExprSet bodyCnjs;
        getConj(hr.body, bodyCnjs);
        for (auto bc : bodyCnjs) {
          if (isOpX<OR>(bc)) {
            ExprSet bcDisj;
            getDisj(bc, bcDisj);
            for (auto bcd : bcDisj) {
              if (isOpX<EXISTS>(bcd) || isOpX<FORALL>(bcd)) {
                preconds.push_back(replaceAll(bcd, hr.dstVars, ruleManager.invVars[invRel]));
              }
            }
          }
        }
      }
      
      if (preconds.size() != 2 || invRel == nullptr) {
        return Result_t::UNKNOWN;
      }

      // outs() << "solveWithPreHelper precondn: " << *disjoin(preconds, m_efac) << endl;

      ExprSet qvars1;
      ExprSet qvars2;
      getQuantifiedVars(preconds[0], qvars1);
      getQuantifiedVars(preconds[1], qvars2);
      
      ExprSet itrVars;
      bool itrUp = invItrInc[invRel];
      for (auto i = 0; i < ruleManager.chcs.size(); i++) {
        auto & hr = ruleManager.chcs[i];
        if (!hr.isInductive) continue;
        copy(invItrs[make_pair(i,hr.srcRelations[0])].begin(),
             invItrs[make_pair(i,hr.srcRelations[0])].end(),
             inserter(itrVars, itrVars.end()));
      }

      ExprVector rfs;
      for (auto qv1 : qvars1) {
        for (auto iv : itrVars) {
          for (auto qv2 : qvars2) {
            if (itrUp) {
              rfs.push_back(mk<LT>(qv1, iv));
              rfs.push_back(mk<LT>(qv2, iv));
            } else {
              rfs.push_back(mk<GT>(qv1, iv));
              rfs.push_back(mk<GT>(qv2, iv));              
            }
          }
        }
      }

      ExprSet qCands;
      getQueryArrayCandidates(qCands);
      Expr qCand = conjoin(qCands, m_efac);
      
      // Expr pre = disjoin(preconds, m_efac);
      for (int i = 0; i < preconds.size(); i++) {
        Expr otherPre = preconds[1-i];
        Expr pre = preconds[i];
        Expr preWithRange;
        ExprVector args;
        Expr qCandNew;
        for (int j = 0; j < pre->arity() - 1; j++) {
          args.push_back(pre->arg(j));
        }
        if (isOpX<EXISTS>(pre)) {
          args.push_back(mk<AND>(pre->last(), mkNeg(rfs[i])));
          preWithRange = mknary<EXISTS>(args);
        } else {
          args.push_back(mk<OR>(pre->last(), mkNeg(rfs[i])));
          preWithRange = mknary<FORALL>(args);
        }
        
        args.clear();
        for (int j = 0; j < qCand->arity() - 1; j++) {
          args.push_back(qCand->arg(j));
        }
        if (isOpX<EXISTS>(qCand)) {
          args.push_back(mk<AND>(qCand->last(), rfs[i]));
          qCandNew = mknary<EXISTS>(args);
        } else {
          args.push_back(mk<OR>(qCand->last(),  rfs[i]));
          qCandNew = mknary<FORALL>(args);
        }
        
        candidates[invRel].clear();
        // outs() << "otherPre: " << *otherPre << endl;
        // outs() << "preWithRange: " << *preWithRange << endl;
        candidates[invRel].insert(mk<OR>(otherPre, preWithRange, qCandNew));
        if (checkAllOver(true)) {
          return Result_t::UNSAT;
        }          
      }

      return Result_t::UNKNOWN;      
    }

    //checks if an invariant can be found for precond
    //if invProp is set property will be inverted
    Result_t solveWithPre(Expr precond, bool invProp)
    {
      Expr post;
      Expr loopCondn;
      splitQueryBody(post, loopCondn);      
      string newChcFile = constructRules(post, loopCondn, precond, invProp);      
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newChcFile);
      NonlinCHCsolver newNonlin(nrm, 1);
      newNonlin.initShapeAbduction();

      return newNonlin.solveWithPreHelper();
    }
    
    Result_t weakenCtm(map<Expr, ExprSet> & invSoln, Expr & ctm, const string & inverseFile)
    {
      if (isOpX<TRUE>(ctm)) {
        return Result_t::UNSAT;
      }
      
      //execute with ctm as initial condition to determine whether ctm can be in pre or cpre
      bool prectm;      
      Result_t res1 = executeChc(ctm, false); // try with property
      Result_t res2 = Result_t::UNKNOWN;
      if (res1 == Result_t::UNKNOWN) {
        res2 = executeChc(ctm, true); // try with negation of property
      }
      
      if (res1 == Result_t::SAT || res2 == Result_t::UNSAT) {
        prectm = false;
      } else if (res2 == Result_t::SAT || res1 == Result_t::UNSAT) {
        prectm = true;
      } else {
        return Result_t::UNKNOWN;
      }      
      
      //weaken pre or cpre using sygus
      Expr pRel = getPrecondnRel();
      Expr weakprecond = sygusWeaken(ctm, prectm);
      outs() << "weakprecond: " << *weakprecond << endl;
      if (isOpX<TRUE>(weakprecond)) {
        return Result_t::UNKNOWN;
      }
      
      Expr curprecond = prectm ?  conjoin(candidates[pRel], m_efac) : conjoin(invSoln[pRel], m_efac);
      Expr newprecond = mk<OR>(weakprecond, curprecond);
      
      //find invariant by solving original or inverted chc system
      Result_t res = solveWithPre(newprecond, !prectm);
      
      if (res == Result_t::UNSAT) {
        if (prectm) {
          candidates[pRel].clear();
          candidates[pRel].insert(newprecond);
        } else {
          invSoln[pRel].clear();
          invSoln[pRel].insert(newprecond);
        }
      }
      
      return res;
    }

    string writeInverseFile(Expr precond = nullptr)
    {
      Expr post;
      Expr loopCondn;
      splitQueryBody(post, loopCondn);
      string inverseFile = constructRules(post, loopCondn, precond);
      outs() << "dumped to: " <<  inverseFile << "\n";
      return inverseFile;

    }

    string writeFile(Expr precond = nullptr)
    {
      Expr post;
      Expr loopCondn;
      splitQueryBody(post, loopCondn);
      string f = constructRules(post, loopCondn, precond, false);
      outs() << "dumped to: " <<  f << "\n";
      return f;
    }    

    void initNondetChc()
    {
      for (int hrIndex1 = 0; hrIndex1 < ruleManager.chcs.size(); hrIndex1++) {   
        auto & hr1 = ruleManager.chcs[hrIndex1];        
        if (hr1.isQuery || hr1.isFact || hr1.srcRelations[0] != hr1.dstRelation) continue;
        //nondetChcGuard.insert(pair<int, Expr>(hrIndex1, mk<TRUE>(m_efac)));
        bool pairFound  = false;
        for (int hrIndex2 = 0; hrIndex2 < ruleManager.chcs.size(); hrIndex2++) {                   
          auto & hr2 = ruleManager.chcs[hrIndex2];
          if (hrIndex1 == hrIndex2 || hr2.isQuery || hr2.isFact ||
              hr2.srcRelations[0] != hr2.dstRelation ||
              hr2.dstRelation != hr1.dstRelation)
            continue;
          vector<int> guardpair;
          guardpair.push_back(hrIndex2);
          nondetChcPair.insert(pair<int,vector<int> >(hrIndex1, guardpair));
          pairFound = true;
        }
        if (pairFound) {
          nondetChcGuard.insert(pair<int, Expr>(hrIndex1, mk<TRUE>(m_efac)));
        }
      }

      for (auto p : nondetChcPair) {
        outs() << endl << p.first << ": ";
        for (auto ps : p.second) {
          outs() << ps << ",";
        }
      }
    }

    //skip cand if the range in cand is not in the direction of itrUp
    //if invert is given then skip if it is in the direction
    bool skipCandidate(Expr cand, ExprVector qvars, ExprVector itrvars, bool itrUp, bool invert)
    {
      if (!containsOp<ARRAY_TY>(cand)) return true;
      
      Expr range = itrUp ? mk<LT>(qvars[0], itrvars[0]) : mk<GT>(qvars[0], itrvars[0]);
      Expr candRange = getArrayOrRange(cand);
      if (isOpX<FORALL>(cand)) candRange = mkNeg(candRange);
      bool samedirection = (bool) u.isSat(candRange, range);
      return samedirection == invert;
    }

    //plain decomposition
    void multiabdarr(vector<ExprVector> rargs, Expr concl, ExprVector & soln)
    {
      ExprSet allargs;
      for (auto rarg : rargs) {
        copy(rarg.begin(), rarg.end(), inserter(allargs, allargs.begin()));
      }

      if (allargs.size() == rargs[0].size()) {
        //nothing much to do
        soln.push_back(concl);
        for (int i = 1; i < rargs.size(); i++) {
          soln.push_back(mk<TRUE>(m_efac));
        }
        return;
      }

      //get an initial solution (which is just the model)
      assert(u.isSat(concl) && "conclusion is not sat in multiabdarr");
      ExprVector tmpsoln;
      for (int i = 0; i < rargs.size(); i++) {
        for (int j = 0;j < rargs[i].size(); j++) {
          tmpsoln.push_back(mk<EQ>(rargs[i][j], u.getModel(rargs[i][j])));
        }
      }

      //extend model to maximal by simple abduction for each relation
      for (int i = 0; i < rargs.size(); i++) {
        ExprSet cnjs;
        for (int j = 0; j < rargs.size(); j++) {
          if (j != i) {
            cnjs.insert(tmpsoln[j]);
          }
        }
        cnjs.insert(mkNeg(concl));
        ExprVector elimVars;
        for (auto arg : allargs) {
          if (emptyIntersect(arg, rargs[i])) {
            elimVars.push_back(arg);
          }
        }
        soln.push_back(keepQuantifiersRepl(conjoin(cnjs, m_efac), elimVars));
      }              
    }
    
    void abduceNondet(const int hrIndex, bool computeGuard = false)
    {
      auto & hr = ruleManager.chcs[hrIndex];
      
      if (hr.isFact) return;

      if (hr.isQuery) {
        getQueryArrayCandidates(candidates[hr.srcRelations[0]]);
        return;
      }

      Expr dstRel = hr.dstRelation;
      Expr srcRel = hr.srcRelations[0];
      bool precondcompute = srcRel == getPrecondnRel();
      bool posttosrc = (srcRel != nullptr && srcRel != dstRel && !precondcompute);
      bool updated = false;
      
      ExprSet dstCands;
      for (auto c : candidates[dstRel]) {
        dstCands.insert(simplifyBool(simplifyArithm(c)));
      }

      ExprSet candidatesTmp;
      for (auto c : candidates[srcRel]) {
        candidatesTmp.insert(c);
      }

      bool nondetChc = false;
      Expr nondetGuard = nullptr;
      auto nondetChcGuardItr = nondetChcGuard.find(hrIndex);
      if (nondetChcGuardItr != nondetChcGuard.end()) {
        nondetChc = true;
        Expr nci = nondetChcGuardItr->second;
        if(!isOpX<TRUE>(nci)) {
          nondetGuard = nci;
        }
      }
      
      boost::tribool forall(boost::indeterminate);
      
      for (auto dc : dstCands) {
        ExprSet dcDisjs;
        getDisj(dc, dcDisjs);

        for (auto dcd : dcDisjs) {
          if (isOpX<FORALL>(dcd)) {
            forall = true;
          } else if (isOpX<EXISTS>(dcd)) {
            forall = false;
          } else {
            //TODO: handle non quantified case
            continue;
          }

          outs () << ">>>>>>>>>>>>>> next cand: "<< dcd<<"\n";

          ExprSet qVarsTmp;
          getQuantifiedVars(dcd, qVarsTmp);
          ExprVector qVars(qVarsTmp.begin(), qVarsTmp.end());
          // ExprVector & itrVars = invItrs[make_pair(hrIndex, srcRel)];
          ExprVector itrVars;
          if (posttosrc) {
            for (auto i = 0; i < ruleManager.chcs.size(); i++) {
              if(invItrs[make_pair(i,srcRel)].size() != 0) {
                copy(invItrs[make_pair(i,srcRel)].begin(),
                     invItrs[make_pair(i,srcRel)].end(),
                     inserter(itrVars, itrVars.end()));
                break;
              }
            }
          } else {
            for (auto iv : invItrs[make_pair(hrIndex, srcRel)]) {
              itrVars.push_back(iv);
            }
          } 
          
          ExprVector & sizeVars = invSizeVars[srcRel];
          bool itrUp = invItrInc[srcRel];

          ExprVector itrVarsDst;
          bool itrUpDst = invItrInc[dstRel];
          for (auto i = 0; i < ruleManager.chcs.size(); i++) {
            copy(invItrs[make_pair(i,dstRel)].begin(),
                 invItrs[make_pair(i,dstRel)].end(),
                   inserter(itrVarsDst, itrVarsDst.end()));
          }
          
          if (skipCandidate(dcd, qVars, itrVarsDst, itrUpDst, precondcompute || posttosrc)) {
            continue;
          }

          ExprVector arrayFormulas;
          Expr dcdm = dcd->last();
          Expr dcda = nullptr;
          Expr dcdr = nullptr;
          bool dcdOr;
          {
            ExprSet dcdms;
            if (isOpX<OR>(dcdm)) {
              dcdOr = true;
              getDisj(dcdm, dcdms);
            } else {
              dcdOr = false;
              getConj(dcdm, dcdms);
            }
            ExprSet dcdma;
            ExprSet dcdmr;
            for (auto d : dcdms) {
              if (containsOp<ARRAY_TY>(d)) {
                dcdma.insert(d);
              } else if (emptyIntersect(d, itrVars)) {
                dcdmr.insert(d);
              }
            }
            dcda = dcdOr ? disjoin(dcdma, m_efac) : conjoin(dcdma, m_efac);
            dcdr = dcdOr ? disjoin(dcdmr, m_efac) : conjoin(dcdmr, m_efac);
            outs() << "dcda: " << *dcda << endl;
            outs() << "dcdr: " << *dcdr << endl;
          }
          
          arrayFormulas.push_back(getArrayFormula(hr,
                                                  precondcompute ? dcd->last() : dcda,
                                                  AbdType::REAL,
                                                  qVars,
                                                  itrVars,
                                                  computeGuard ? nondetGuard : nullptr));

          if (isOpX<FALSE>(arrayFormulas[0]) && !precondcompute && !posttosrc)
          {
            outs () << "vacuous1\n";

            // if (precondcompute) continue;
            
            if (!nondetChc || nondetGuard == nullptr || !computeGuard) {
              //todo: handle this case
              // return;
              continue;
            }
            arrayFormulas.pop_back();
            Expr naf = replaceAll(nondetGuard, hr.srcVars[0], ruleManager.invVars[hr.srcRelations[0]]);
            naf = replaceAll(naf, itrVars, qVars);
            naf = mkNeg(naf);
            arrayFormulas.push_back(naf);
          }
          
          if (!precondcompute && !posttosrc && nondetChc && nondetGuard == nullptr && computeGuard) {
            Expr nguard = arrayFormulas[0];
            nguard = replaceAll(nguard, qVars, itrVars);
            nguard = replaceAll(nguard, ruleManager.invVars[hr.srcRelations[0]], hr.srcVars[0]);
            
            /* at present use srcVars to both inv and guards; in future extend to get this from user */
            vector<ExprVector> relargs;
            relargs.push_back(hr.srcVars[0]);
            relargs.push_back(hr.srcVars[0]);
            ExprVector soln;
            multiabdarr(relargs, nguard, soln);
            nondetChcGuard[hrIndex] = soln[0];            
            if (nondetChcPair.find(hrIndex) != nondetChcPair.end()) {
              vector<int> phrindcs = nondetChcPair[hrIndex];
              vector<ExprVector> grelargs;              
              for (auto i = 0; i < phrindcs.size(); i++) {
                grelargs.push_back(hr.srcVars[0]);
              }                
              ExprVector gsoln;
              multiabdarr(grelargs, mkNeg(nondetChcGuard[hrIndex]), gsoln);
              for (auto i = 0; i < phrindcs.size(); i++) {
                auto phrIndex = phrindcs[i];
               auto & phr = ruleManager.chcs[phrindcs[i]];               
               nondetChcGuard[phrIndex] = replaceAll(gsoln[i], hr.srcVars[0], phr.srcVars[0]);
              }
            }            
            return;
            // if (forall)
            //   return;
          }
              
          
          if (precondcompute || posttosrc) {
            arrayFormulas.push_back(getArrayFormula(hr, dcd->last(), AbdType::MOCK, qVars, itrVars));
            if (isOpX<FALSE>(arrayFormulas[1])) {
              outs () << "vacuous2\n";
              continue;
            }              

            for (auto qv : qVars) {
              ExprVector args1 = {qv->left()};
              bool itrUp = invItrInc[srcRel];
              Expr newCondn = nullptr;
              if (posttosrc) {
                newCondn = itrUp ? mk<LT>(qv, itrVars[0]) : mk<GT>(qv, itrVars[0]);
              }              
              if (forall == true)
              {
                if (posttosrc) {
                  args1.push_back(mk<OR>(arrayFormulas[1], mkNeg(newCondn)));
                } else {
                  args1.push_back(arrayFormulas[1]);
                }
                if (containsOp<ARRAY_TY>(arrayFormulas[1])) {
                  candidatesTmp.insert(mknary<FORALL>(args1));
                } 
              } else if (forall == false)
              {                
                if (posttosrc) {
                  args1.push_back(mk<AND>(arrayFormulas[1], newCondn));
                } else {
                  args1.push_back(arrayFormulas[1]);
                }
                Expr acand = nullptr;
                if (containsOp<ARRAY_TY>(arrayFormulas[1])) {
                  acand = mknary<EXISTS>(args1);
                  if (posttosrc) {
                    ExprVector args2 = {qv->left()};
                    dcdr = replaceAll(dcdr, ruleManager.invVars[dstRel], ruleManager.invVars[srcRel]);
                    outs() << *dcdr << endl;
                    args2.push_back(mk<AND>(mkNeg(newCondn), dcdr));
                    acand = mk<OR>(acand, mknary<EXISTS>(args2));                    
                  }
                }                
                if (acand != nullptr)
                  candidatesTmp.insert(acand);
              }
            }
            continue;
          }

          for (auto qv : qVars) {
            for (auto iv : itrVars) {
              Expr rf;
              if (itrUp) {
                rf = mk<GEQ>(qv,iv);
              } else {
                rf = mk<LEQ>(qv,iv);
              }

              Expr extraCondn = mk<TRUE>(m_efac);
              if (hr.isInductive) {
                ExprSet extraCondns;
                ExprSet bodyConj;
                getConj(hr.body, bodyConj);
                for (auto bc : bodyConj) {
                  if (!emptyIntersect(bc, itrVars) && !isOpX<EQ>(bc)) {
                    extraCondns.insert(replaceAll(bc, itrVars, qVars));
                  }
                }
                extraCondn = conjoin(extraCondns, m_efac);
              }

              Expr af = dcdOr ? mk<OR>(dcdr, arrayFormulas[0]) : mk<AND>(dcdr, arrayFormulas[0]);
              
              outs() << "RF: " << *rf << "\n";
              outs() << "AF0: " << *(af) << "\n";
              
              ExprVector args1 = {qv->left()};
              if (forall == true)
              {
                if (hr.isInductive)
                {
                  extraCondn = mkNeg(extraCondn);
                  args1.push_back(mk<OR>(af, mk<NEG>(rf), extraCondn));
                  if (containsOp<ARRAY_TY>(af))
                    candidatesTmp.insert(mknary<FORALL>(args1));
                }
                else
                {
                  args1.push_back(af);
                  if (containsOp<ARRAY_TY>(af)) {
                    candidatesTmp.insert(mknary<FORALL>(args1));
                  }
                }
              } else if (forall == false) {
                if (hr.isInductive)
                {
                  args1.push_back(mk<AND>(af, rf, extraCondn));
                  candidatesTmp.insert(mknary<EXISTS>(args1));
                }
                else
                {
                  bool cp1 = containsOp<ARRAY_TY>(af);
                  args1.push_back(af);
                  if (cp1) 
                    candidatesTmp.insert(mknary<EXISTS>(args1));                  
                }
              }
            }
          }
        }
        // if (!precondcompute && !posttosrc) {
        //   //shape abduction does abduction to only first candidate if it is not precondition computation
        //   break;
        // }
      }

      if (candidatesTmp.size() == candidates[srcRel].size()) return;
      
      candidates[srcRel].clear();
      for (auto itr = candidatesTmp.begin(); itr != candidatesTmp.end();)
      {
        if (u.isTrue(*itr) || u.isFalse(*itr)) {
          itr = candidatesTmp.erase(itr);
        } else {
          ++itr;
        }
      }
      if (forall == true) {
        for (auto c : candidatesTmp) {
          candidates[srcRel].insert(c);
        }
      } else {
        ExprSet cdisj;
        for (auto c : candidatesTmp) {
          ExprSet cd;
          getDisj(c, cd);
          for (auto cdItr = cd.begin(); cdItr != cd.end();) {
            if (!containsOp<ARRAY_TY>(*cdItr) && !posttosrc && !updated) {
              cdItr = cd.erase(cdItr);
            } else {
              ++cdItr;
            }
          }
          cdisj.insert(disjoin(cd, m_efac));
        }
        candidates[srcRel].insert(disjoin(cdisj, m_efac));
      }
    }

    bool equalGuards(map<int, Expr> ng)
    {
      
      if (nondetChcGuard.size() != ng.size()) return false;
      
      for (auto ngi : ng) {
        if (!isOpX<TRUE>(nondetChcGuard[ngi.first]) && isOpX<TRUE>(ngi.second)) { //the other way shouldn't happen
          return false;
        }
      }
      return true;
    }

    Expr getArrayOrRange(Expr qf, bool array = false)
    {
      assert(isOpX<FORALL>(qf) || isOpX<EXISTS>(qf));
      
      Expr qfm = qf->last();
      bool qfor = isOpX<OR>(qfm) ? true : false;
      ExprSet qfms;
      if (isOpX<OR>(qfm)) {
        qfor = true;
        getDisj(qfm, qfms);
      } else if (isOpX<AND>(qfm)) {
        qfor = false;
        getConj(qfm, qfms);
      } else {
        assert(0 && "only or and operations are supported");
      }

      ExprSet res;
      for (auto q : qfms) {
        bool add = array == containsOp<ARRAY_TY>(q);
        if (add) {
          res.insert(q);
        }
      }      
      Expr retres =  qfor ? disjoin(res, m_efac) : conjoin(res, m_efac);
      outs() << "retres: " << *retres << endl;
      return retres;
    }

    

    void forwardPropagate(int hrIndex)
    {

      auto & hr = ruleManager.chcs[hrIndex];
      // Expr cti = u.getModel(hr.dstVars);
      ExprSet dstcands = candidates[hr.dstRelation];
      Expr initic = nullptr;
      Expr initqc = nullptr;
      bool forall = false;
      {
        ExprSet tmpcnjs;
        ExprVector tmpinitic;
        ExprVector tmpinitqc;
        getConj(hr.body, tmpcnjs);
        for (auto c : tmpcnjs) {
          if (containsOp<FORALL>(c) || containsOp<EXISTS>(c)) {
            tmpinitqc.push_back(c);
          } else {
            tmpinitic.push_back(c);
          }
        }
        initic = conjoin(tmpinitic, m_efac);
        initqc = conjoin(tmpinitqc, m_efac);
      }
      //assumption: we will have some int and quantified conditions in hr.body
      assert(initic != nullptr && initqc != nullptr);

      outs() << "initic: " << *initic << endl;
      outs() << "initqc: " << *initqc << endl;
        
      Expr invrange = nullptr;
      for (auto cnj : dstcands) {
        ExprSet dstcand;
        getDisj(cnj, dstcand); 
        for (auto dc : dstcand) {
          outs() << *dc << endl;
          if (isOpX<FORALL>(dc) || isOpX<EXISTS>(dc)) {
            forall = isOpX<FORALL>(dc) ? true : false;
            Expr d = replaceAll(dc, ruleManager.invVars[hr.dstRelation], hr.dstVars);
            if (u.isTrue(mk<AND>(initic, d)) || u.isFalse(mk<AND>(initic, d))) continue;
            invrange = getArrayOrRange(dc);
          } else {
            continue;
          }
          if (invrange != nullptr) break;
        }
        if (invrange != nullptr) break;
      }            
      assert(invrange != nullptr);

      ExprSet weakeraf;
      {
        Expr dstannot = replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars);
        dstannot = mkNeg(dstannot);
        dstannot = mk<AND>(initic, dstannot);
        ExprSet precnjs;
        getConj(initqc, precnjs);
        for (auto precnj : precnjs) {
          ExprSet predisjs;
          getDisj(precnj, predisjs);
          for (auto predisj : predisjs) {
            if (isOpX<FORALL>(predisj) || isOpX<EXISTS>(predisj)) {
              //todo: use cti instead
              if (u.isSat(predisj, dstannot)) {
                Expr af = getArrayOrRange(predisj, true);
                af = replaceAll(af, hr.dstVars, ruleManager.invVars[hr.dstRelation]);
                weakeraf.insert(af);
              }
            }
          }
        }
      }

      
      for (auto w : weakeraf) {
        ExprSet allVars;
        filter(w, bind::IsConst(), inserter(allVars, allVars.begin()));
        ExprVector qVars;
        copy(allVars.begin(), allVars.end(), inserter(qVars, qVars.begin()));        
        for (auto qitr = qVars.begin(); qitr != qVars.end();) {
          bool erased = false;
          for (auto iv : ruleManager.invVars[hr.dstRelation]) {
            if (*qitr == iv) {
              qitr = qVars.erase(qitr);
              erased = true;
              break;
            } 
          }
          if (!erased) {
            ++qitr;
          }
        }
        ExprVector qargs;
        for (auto qv : qVars) {
          qargs.push_back(qv->left());
        }
        Expr newcand = nullptr;
        if (forall) {
          qargs.push_back(mk<OR>(invrange, w));
          newcand = mknary<FORALL>(qargs);
        } else {
          qargs.push_back(mk<AND>(invrange, w));
          newcand = mknary<EXISTS>(qargs);
        }
        if (newcand != nullptr) {
          ExprSet candsTmp;
          for (auto c : candidates[hr.dstRelation]) {
            candsTmp.insert(c);
          }
          candidates[hr.dstRelation].clear();
          for (auto c : candsTmp) {
            ExprSet cd;
            getDisj(c, cd);
            for (auto cdItr = cd.begin(); cdItr != cd.end();) {
              if (!containsOp<ARRAY_TY>(*cdItr)) {
                cdItr = cd.erase(cdItr);
              } else {
                ++cdItr;
              }
            }
            candidates[hr.dstRelation].insert(mk<OR>(disjoin(cd, m_efac), newcand));
          }
        }
      }                     
    }
    
    Result_t inferInvNondet(bool computeGuard = true)
    {
      vector<int> retrylist;
      for (int i = 0; i < propOrder.size(); i++) {
        int hrIndex = propOrder[i];
        auto & hr = ruleManager.chcs[hrIndex];
        outs () << "\n\n\n===============\ninferInvNondet for chc:  " <<
          (hr.srcRelations.empty() ? "" : lexical_cast<string>(hr.srcRelations[0]))
                << " -> " << hr.dstRelation << "\n";

        outs() << "\n\n hr.body " << *(hr.body) <<  "\n\n";
        auto candidatesTmp = candidates;
        auto ncgTmp = nondetChcGuard;
        if (!hr.srcRelations.empty())
        {
          outs () << "cands [src]:  \n";
          pprint(candidates[hr.srcRelations[0]], 2);
          if (hr.srcRelations[0] != hr.dstRelation)
          {
            outs () << "cands [dst]:  \n";
            pprint(candidates[hr.dstRelation], 2);
          }
        }

        bool res = checkCHC(hr, candidates, true, computeGuard, hrIndex);
        if (!res) {
          if (hr.isFact) {
            forwardPropagate(hrIndex);
            outs() << "\n dst->";
            pprint(candidates[hr.dstRelation], 2);
          } else {
            abduceNondet(hrIndex, computeGuard);
            outs() << "\n src->";
            pprint(candidates[hr.srcRelations[0]], 2);
            outs() << "\n dst->";
            pprint(candidates[hr.dstRelation], 2);
            for (auto ng : nondetChcGuard) {
              outs() << ng.first << " -> " << ng.second << endl;
            }
          }
                 
          //no new candidate; perhaps, try later again if others get
          if (equalCands(candidatesTmp) && (!computeGuard || equalGuards(ncgTmp))) {
            retrylist.push_back(hrIndex);
            //break;
          } else {
            if (retrylist.size() == 0) continue;
            vector<int> tmppo;
            for (int j = 0; j < retrylist.size(); j++) {
              tmppo.push_back(retrylist[j]);
            }
            for (int j = i+1; j < propOrder.size(); j++) {
              tmppo.push_back(propOrder[j]);
            }
            for (int j = 0; j < tmppo.size(); j++) {
              propOrder.insert(propOrder.begin()+i+j+1, tmppo[j]);
            }
            retrylist.clear();
          }
        }
      }

      // double check
      filterUnsat();
      if (checkAllOver(true, false, computeGuard)) {
        printCands();
        dumpSmt(computeGuard);
        return Result_t::UNSAT;
      } else {
        outs () << "unknown\n";
        return Result_t::UNKNOWN;
      }
    }

    Result_t solveInverseNondetMax(const string & inverseFile)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(inverseFile);
      NonlinCHCsolver newNonlin(nrm, 1);
      newNonlin.initNondetChc();
      newNonlin.initShapeAbduction();
      return newNonlin.inferInvNondet();
    }

    Result_t verifyPre(string newfile)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newfile);
      NonlinCHCsolver newNonlin(nrm, 1);
      newNonlin.initShapeAbduction();
      return newNonlin.inferInvNondet(false);
    }

    void getCandWeakPre(ExprSet & candpres)
    {
      Expr pRel = getPrecondnRel();
      ExprSet & cands = candidates[pRel];
      for (auto itr = cands.begin(); itr != cands.end();)
      {
        if (u.isTrue(*itr) || u.isFalse(*itr)) {
          itr = cands.erase(itr);
        } else {
          ++itr;
        }
      }
      //compute all subsets
      ExprVector candsTmp(cands.begin(), cands.end());
      int powsize = pow(2, candsTmp.size());
      for (int i = 0; i < powsize; i++) {
        ExprSet cnjs;
        for (int j = 0; j < candsTmp.size(); j++) {
          if ((i & (1 << j)) != 0) {
            cnjs.insert(candsTmp[j]);
          }
        }
        if (cnjs.size() == candsTmp.size()) continue;
        candpres.insert(conjoin(cnjs, m_efac));
      }
    }
    
    Result_t weakenPreNondet()
    {
      ExprSet candpres;
      getCandWeakPre(candpres);
      for (auto candpre : candpres) {
        string newfile = writeFile(candpre);
        Result_t preverified = verifyPre(newfile);
        if (preverified == Result_t::UNSAT) {
          Expr pRel = getPrecondnRel();
          candidates[pRel].clear();
          ExprSet pres;
          getConj(candpre, pres);
          for (auto pre : pres) {
            candidates[pRel].insert(pre);
          }
          return Result_t::UNSAT;
        }
      }
      return Result_t::UNKNOWN;
    }
    
    void checkMaximalityNondet()
    {
      bool max = false;
      do {
        Expr curpre = conjoin(candidates[getPrecondnRel()], m_efac);
        if (u.isTrue(curpre)) {
          outs() << "maximal!\n";
          max = true;
          printCands();
          break;
        }
        string inverseFile = writeInverseFile(mkNeg(curpre));
        Result_t maxRes = solveInverseNondetMax(inverseFile);
        if (maxRes == Result_t::UNSAT) {
          outs() << "maximal!\n";
          max = true;
          printCands();
        } else {
          outs() << "checking nm\n";
          Result_t nonmaxRes = weakenPreNondet();
          if (nonmaxRes == Result_t::UNSAT) {
            max = false;
          } else {
            outs() << "may not be maximal\n";
            break;
          }
        }
      } while(!max);
    }

    void checkMaximality()
    {
      string inverseFile = writeInverseFile();
      map<Expr, ExprSet> invSoln;
      Result_t res = solveInverse(inverseFile, invSoln);
      Expr ctm = mk<TRUE>(m_efac);
      if (res == Result_t::UNSAT) {
        bool maximal = false;
        while (weakenCtm(invSoln, ctm, inverseFile) == Result_t::UNSAT) {
          if (pWeakCheck(invSoln, ctm)) {
            maximal = true;
            break;
          }
        }
        if (maximal) {
          outs() << "maximal!\n";
        } else {
          outs() << "not-max\n";
        }
      } else {
        outs() << "may not be maximal\n";
      }
    }

    void persistCands(string smt)
    {
      string output = smt.substr(smt.find_last_of("/"));
      output = "/tmp/" + output.substr(0, output.find_last_of("."));
      output += ".result";
      ofstream outputfile(output);
      printCands(outputfile, false, true);
      outputfile.close();
    }

    //Backward and forward, multiple CHC propagation
    void guessAndSolve()
    {
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }

      while (true)
      {
        auto candidatesTmp = candidates;
        for (bool fwd : { false, true })
        {
          if (debug)
          {
            outs () << "\n\n\n  ####   ITER   ####   " << globalIter << "." << fwd << "   ####\nCurrent candidates:\n";
            printCands(false);
          }
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
          propagate(fwd);
          filterUnsat();
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
          if (checkAllOver(true)) return printCands();
        }
        if (equalCands(candidatesTmp)) break;
        globalIter++;
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return printCands();
      outs () << "unknown\n";
    }

    // naive solving, without invariant generation
    int solveIncrementally(int bound, int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > bound)       // maximum bound reached
      {
        return 2;
      }
      else if (rels.empty()) // base case == init is reachable
      {
        return 0;
      }

      int res = 1;

      // reserve copy;
      auto ssaStepsTmp = ssaSteps;
      int varCntTmp = varCnt;

      vector<vector<int>> applicableRules;
      for (int i = 0; i < rels.size(); i++)
      {
        vector<int> applicable;
        for (auto & r : ruleManager.incms[rels[i]])
        {
          Expr body = ruleManager.chcs[r].body; //ruleManager.getPostcondition(r);
          if (args.size() != 0)
            body = replaceAll(body, ruleManager.chcs[r].dstVars, args[i]);
          // identifying applicable rules
          if (u.isSat(body, conjoin(ssaSteps, m_efac)))
          {
            applicable.push_back(r);
          } 
        }
        if (applicable.empty())
        {
          return 1;         // nothing is reachable; thus it is safe here
        }
                
        applicableRules.push_back(applicable);
      }

      vector<vector<int>> ruleCombinations;
      getCombinations(applicableRules, ruleCombinations);

      for (auto & c : ruleCombinations)
      {
        ssaSteps = ssaStepsTmp;
        varCnt = varCntTmp;
        ExprVector rels2;
        vector<ExprVector> args2;

        for (int i = 0; i < c.size(); i++)
        {
          // clone all srcVars and rename in the body
          auto &hr = ruleManager.chcs[c[i]];
          Expr body = hr.body;
          if (!hr.dstVars.empty()) body = replaceAll(body, hr.dstVars, args[i]);
          vector<ExprVector> tmp;
          for (int j = 0; j < hr.srcRelations.size(); j++)
          {
            rels2.push_back(hr.srcRelations[j]);
            ExprVector tmp1;
            for(auto &a: hr.srcVars[j])
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              tmp1.push_back(cloneVar(a, new_name));
            }
            args2.push_back(tmp1);
            body = replaceAll(body, hr.srcVars[j], tmp1);
            for (auto & a : hr.locVars)
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              body = replaceAll(body, a, cloneVar(a, new_name));
            }
          }

          ssaSteps.push_back(body);
        }
        
        if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
        {
          int res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
          if (res_tmp == 0) return 0;           // bug is found for some combination
          else if (res_tmp == 2) res = 2;
        }
      }
      return res;
    }

    // naive solving, without invariant generation
    int solveIncrementally(int bound)
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      return solveIncrementally (bound, 0, query, empt);
    }
    
    void initDumpSmt(bool dumpsmtIn)
    {
      dumpsmt = dumpsmtIn;
    }
    
    void dumpSmt(bool guardcompute)
    {
      if (!dumpsmt || guardcompute) return;
      Expr post;
      Expr loopCondn;
      splitQueryBody(post, loopCondn);
      Expr precond = conjoin(candidates[getPrecondnRel()], m_efac);
      constructRules(post, loopCondn, precond, false, "_bench");
    }

    void checkNondet()
    {
      bool nondet = false;
      
      for (int hrIndex1 = 0; hrIndex1 < ruleManager.chcs.size(); hrIndex1++) {   
        auto & hr1 = ruleManager.chcs[hrIndex1];        
        if (hr1.isQuery || hr1.isFact || hr1.srcRelations[0] != hr1.dstRelation) continue;
        for (int hrIndex2 = 0; hrIndex2 < ruleManager.chcs.size(); hrIndex2++) {                   
          auto & hr2 = ruleManager.chcs[hrIndex2];
          if (hrIndex1 == hrIndex2 || hr2.isQuery || hr2.isFact ||
              hr2.srcRelations[0] != hr2.dstRelation ||
              hr2.srcRelations[0] != hr1.srcRelations[0] || 
              hr2.dstRelation != hr1.dstRelation)
            continue;
          Expr b1 = replaceAll(hr1.body, hr1.srcVars[0], ruleManager.invVars[hr1.srcRelations[0]]);
          Expr b2 = replaceAll(hr2.body, hr2.srcVars[0], ruleManager.invVars[hr2.srcRelations[0]]);
          if (u.isSat(b1, b2)) {
            outs() << "non-deterministic\n" << *(hr1.body) << "\n" << *(hr2.body) << "\n\n";
            return;
          }
        }
      }
      outs() << "Deterministic\n";
    }
  };

  inline void solveNonlin(string smt, int inv, int stren, bool checkmax, bool checkra, bool dumpsmt, bool cndet)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);    
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    
    NonlinCHCsolver nonlin(ruleManager, stren);
    if (inv == 0) {
      clock_t start = clock();
      nonlin.initShapeAbduction();
      nonlin.initDumpSmt(dumpsmt);
      if (cndet) return nonlin.checkNondet();      
      Result_t inferRes = checkra ? nonlin.inferInv() : nonlin.inferInvNondet(false);      
      if (inferRes == Result_t::UNSAT) {
        computetime("pre time: ", start);
        if (checkmax) {
          start = clock();
          nonlin.checkMaximalityNondet();
          computetime("m/n time: ", start);
          nonlin.persistCands(smt);
        }
      }
    } else {
      switch (nonlin.solveIncrementally(inv))
      {
        case 0: outs () << "sat\n"; break;
        case 1: outs () << "unsat\n"; break;
        case 2: outs () << "unknown\n"; break;
      }
    }
  };
}

#endif
