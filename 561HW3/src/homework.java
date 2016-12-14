import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

// TODO: factoring
class Predicate {
	String name;
	ArrayList<String> arguments;
	boolean positive;
	public Predicate(String name, ArrayList<String> arguments, boolean positive) {
		this.name = name;
		this.arguments = arguments;
		this.positive = positive;
	}
	
	public Predicate(Predicate p) {
		name = p.name;
		arguments = new ArrayList<>(p.arguments);
		positive = p.positive;
	}
	
    public String toString() {
    	String res = name + arguments;
    	if(!positive) {
    		res = "~" + res;
    	}
    	return res;
     } 	
}

public class homework {
	
	private static Scanner in;
	private static PrintWriter out;	
	
	public static void main(String[] args) throws FileNotFoundException {
		// TODO Auto-generated method stub
		
		File inputFile = new File("./input.txt");
		in = new Scanner(inputFile);
		out = new PrintWriter("./output.txt");
		
		ArrayList<ArrayList<Predicate>> KB = new ArrayList<>();
		Map<String, Set<Integer>> index = new HashMap<>(); // <Predicate, idxInKB>, predicate could be ~
		ArrayList<Predicate> queryList = new ArrayList<>();
		
		System.out.println("Queries:");
		int numQueries = in.nextInt();
		in.nextLine();
		for (int i = 0; i < numQueries; i++) {
			
			String queryStr = in.nextLine();
			System.out.println(queryStr);
			
			Predicate p = toPredicate(queryStr, 0);
			queryList.add(p);
		}
		
		int namespace = 0;
		
		System.out.println("KB:");
		int numKBs = in.nextInt();
		in.nextLine();
		for (int i = 0; i < numKBs; i++) {
			
			String str = toCNF(in.nextLine());
			System.out.println(str);
			// str is one KB sentence
			String[] sentences = str.split("\\&"); // sentences sharing the same namespace
			for (String sentence : sentences) {
				ArrayList<Predicate> clause = new ArrayList<>();
				String[] predicates = sentence.split("\\|");
				for (String predicate : predicates) {
					Predicate p = toPredicate(predicate, namespace);
					String key = p.name;
					if (!p.positive) {
						key = "~" + key;
					}
					if (!index.containsKey(key)) {
						index.put(key, new HashSet<Integer>());
					}
					index.get(key).add(KB.size());
					clause.add(p);
				}
				KB.add(clause);
			}
			namespace++;
		}
		// now I got the KB
		
		for (int i = 0; i < queryList.size(); i++) {
			
			Predicate p = queryList.get(i);
			p.positive = !p.positive; // negate query
			
			ArrayList<Predicate> negateQueryClause = new ArrayList<>();
			negateQueryClause.add(p);
			

			if (resolution2(new ArrayList<>(KB), copyIndex(index), negateQueryClause)) {
				out.println("TRUE");
				System.out.println("TRUE");
			} else {
				out.println("FALSE");
				System.out.println("FALSE");
			}
		}

		out.close();
	}
	
	// (A=>B) to ((~A)|B)
	// PRE: (...=>...) or A
	private static String eliminateImplications(String s) {
		if (s.indexOf("=>") == -1) return s; 
		// (...=>...)
		int idx = 1;
		if (s.charAt(idx++) == '(') {
			int count = 1;
			while (count > 0) {
				if (s.charAt(idx) == '(') count++;
				else if (s.charAt(idx) == ')') count--;
				idx++;
			}
		} else {
			while (s.charAt(idx) != ')') idx++;
			idx++;
		}// idx == '='
		
		String first = eliminateImplications(s.substring(1, idx));
		String second = eliminateImplications(s.substring(idx + 2, s.length()-1));
		return "(" + "(~" + first + ")" + "|" + second + ")";
	}
	
	// ...(~())...
	private static String moveNotInward(String s, int start) { // test: (~(A|(~(~B))))
		if (start >= s.length()) return "";
		if (start + 1 >= s.length() || !s.substring(start, start + 2).equals("(~")) {
			return s.charAt(start) + moveNotInward(s, start + 1);
		}
		// s.substring(start, start + 2).equals("(~")
		int idx = start + 2;
		int count = 1;
		while (count > 0) {
			if (s.charAt(idx) == '(') count++;
			else if (s.charAt(idx) == ')') count--;
			idx++;
		} // idx - 1 == ')'
		return negate(s.substring(start + 2, idx-1)) + moveNotInward(s, idx);
	}
	
	// PRE: (...) or P(x)
	private static String negate(String s) {
		if (s.charAt(0) != '(') return "(~" + s + ")"; // just one Predicate
		if (s.substring(0,2).equals("(~")) {
			if (s.substring(2,4).equals("(~")) return negate(s.substring(4, s.length()-2)); // (~(~(~A)))...
			return s.substring(2, s.length()-1); // (~(~A)) == A
		} // what if ...
		// (...&...) or (...|...)		
		int idx = 1;
		if (s.charAt(idx++) == '(') {
			int count = 1;
			while (count > 0) {
				if (s.charAt(idx) == '(') count++;
				else if (s.charAt(idx) == ')') count--;
				idx++;
			}
		} else {
			while (s.charAt(idx) != ')') idx++;
			idx++;
		} // idx == '|' or '&'
		
		char operand;
		if (s.charAt(idx) == '|') operand = '&';
		else operand = '|';
		
		String first = negate(s.substring(1, idx));
		String second = negate(s.substring(idx + 1, s.length()-1));
		return "(" + first + operand + second + ")";
	}
	
	// PRE: (...) or P(x)
	private static String distributeOr(String s) { // test: ((A|B)|C), ((A|B)&C), (((A&B)|C)|D)
		if (s.indexOf("&") == -1 || s.indexOf("|") == -1) return s;
		if (s.charAt(1) == '~') return s; // (~A), we moved ~ inward before
		// (...|...) or (...&...) at top level
		int idx = 1;
		if (s.charAt(idx++) == '(') {
			int count = 1;
			while (count > 0) {
				if (s.charAt(idx) == '(') count++;
				else if (s.charAt(idx) == ')') count--;
				idx++;
			}
		} else {
			while (s.charAt(idx) != ')') idx++;
			idx++;
		}// idx == '|' or '&'
		
		String first = distributeOr(s.substring(1, idx)); // A or (~A) or (...&...) // not (...|...), distributed
		String second = distributeOr(s.substring(idx+1, s.length()-1)); // A or (~A) or (...&...)
		if (s.charAt(idx) == '&') {
			return '(' + first + '&' + second + ')';
		}
		// s.charAt(idx) == '|', we need to distribute on the top level, top level operand is '|'
		// (A|B), moveNotInward before...so(~A)
		if ((first.charAt(0) != '(' || first.charAt(1) == '~') && (second.charAt(0) != '(' || second.charAt(1) == '~')) return s;// (A|B)
		if (first.charAt(0) != '(' || first.charAt(1) == '~') { // (A|(...&...)) test: (A|(B&(C&D)))
			// ((first | before&) + & + (first | after&))
			// let's split second into before, operand, after
			int idx2 = 1;
			if (second.charAt(idx2++) == '(') {
				int count2 = 1;
				while (count2 > 0) {
					if (second.charAt(idx2) == '(') count2++;
					else if (second.charAt(idx2) == ')') count2--;
					idx2++;
				}
			} else {
				while (second.charAt(idx2) != ')') idx2++;
				idx2++;
			}// idx2 == '&'
			
			String before = second.substring(1, idx2); // before&
			String after = second.substring(idx2 + 1, second.length()-1); // distributeOr(after)?...
			return "(" + distributeOr("(" + first + "|" + before + ")") + "&" + distributeOr("(" + first + "|" + after + ")") + ")";
		}
		if (second.charAt(0) != '(' || second.charAt(1) == '~') { // ((...&...)|A)
			int idx1 = 1;
			if (first.charAt(idx1++) == '(') {
				int count1 = 1;
				while (count1 > 0) {
					if (first.charAt(idx1) == '(') count1++;
					else if (first.charAt(idx1) == ')') count1--;
					idx1++;
				}
			} else {
				while (first.charAt(idx1) != ')') idx1++;
				idx1++;
			}// idx1 == '&'						
			
			String before = first.substring(1, idx1); // before&
			String after = first.substring(idx1 + 1, first.length()-1);			
			return "(" + distributeOr("(" + before + "|" + second + ")") + "&" + distributeOr("(" + after + "|" + second + ")") + ")";
		}
		// General: ((...&...)|(...&...))
		// ( (firstBefore | secondBefore) & (firstBefore | secondAfter) & (firstAfter | secondBefore) & (firstAfter | secondAfter) )
		// first
		int idx1 = 1;
		if (first.charAt(idx1++) == '(') {
			int count1 = 1;
			while (count1 > 0) {
				if (first.charAt(idx1) == '(') count1++;
				else if (first.charAt(idx1) == ')') count1--;
				idx1++;
			}
		} else {
			while (first.charAt(idx1) != ')') idx1++;
			idx1++;
		}// idx1 == '&'		
		
		String firstBefore = first.substring(1, idx1); // before&
		String firstAfter = first.substring(idx1 + 1, first.length()-1);
		
		// second
		int idx2 = 1;
		if (second.charAt(idx2++) == '(') {
			int count2 = 1;
			while (count2 > 0) {
				if (second.charAt(idx2) == '(') count2++;
				else if (second.charAt(idx2) == ')') count2--;
				idx2++;
			}
		} else {
			while (second.charAt(idx2) != ')') idx2++;
			idx2++;
		}// idx2 == '&'
		
		String secondBefore = second.substring(1, idx2); // before&
		String secondAfter = second.substring(idx2 + 1, second.length()-1);		
		
		return "((("+distributeOr("("+firstBefore+"|"+secondBefore+")")+"&"+
		distributeOr("("+firstBefore+"|"+secondAfter+")")+")"+"&"+
		distributeOr("("+firstAfter+"|"+secondBefore+")")+")"+"&"+
		distributeOr("("+firstAfter+"|"+secondAfter+")")+")"; 
	}
	
	private static String toCNF(String s) {
		String s1 = eliminateImplications(s.replaceAll(" ",""));
		String s2 = moveNotInward(s1, 0);
		return distributeOr(s2);
	}
	
	// string to Predicate
	private static Predicate toPredicate(String s, int namespace) {
		
		boolean positive = true;
		int idx = 0;
		while (!Character.isLetter(s.charAt(idx))) {
			if (s.charAt(idx++) == '~') positive = false;
		}
		int nameStart = idx;
		while (s.charAt(idx) != '(') {
			idx++;
		}
		int pStart = idx;
		String name = s.substring(nameStart, pStart);
		
		while (s.charAt(idx) != ')') {
			idx++;
		}
		String argStr = s.substring(pStart+1, idx).replaceAll(" ", "");
		String[] args = argStr.split(",");
		ArrayList<String> arguments = new ArrayList<>();
		for (String arg : args) {
			if (isVariable(arg)) arg = arg + namespace;
			arguments.add(arg);
		}
		return new Predicate(name, arguments, positive);
	}
	
	private static Map<String, String> unify(Predicate a, Predicate b, Map<String, String> theta) {
		if (theta == null) return null;
		 if ((!a.name.equals(b.name)) || (a.positive != b.positive)) return null;
		return unifyList2(a.arguments, b.arguments, theta);
	}
	
	// PRE: s.length() > 0
	private static boolean isVariable(String s) {
		return Character.isLowerCase(s.charAt(0));
	}
	
	// PRE: used theta to update var before...
	// add clause to KB, and update the index... what if it is already in the KB???
	private static boolean addToKB(ArrayList<ArrayList<Predicate>> KB, Map<String, Set<Integer>> index, ArrayList<Predicate> clause) {
		
		// check if already in KB
		for (ArrayList<Predicate> clauseInKB : KB) {
			if (clauseInKB.toString().equals(clause.toString())) return false;
		}
		
		for (Predicate p : clause) {
			String key = p.name;
			if (!p.positive) {
				key = "~" + key;
			}
			if (!index.containsKey(key)) {
				index.put(key, new HashSet<Integer>());
			}
			index.get(key).add(KB.size());
		}
		KB.add(clause);
		return true;
	}
	
	private static Map<String, Set<Integer>> copyIndex(Map<String, Set<Integer>> map) {
		
		Map<String, Set<Integer>> mapCopy = new HashMap<>();
		for (Map.Entry<String, Set<Integer>> entry : map.entrySet()) {
			Set<Integer> value = new HashSet<>();
			for (int i : entry.getValue()) {
				value.add(i);
			}
			mapCopy.put(entry.getKey(), value);
		}
		return mapCopy;
	}
	
	// PRE: KB and index are copies
	private static boolean resolution2(ArrayList<ArrayList<Predicate>> KB, Map<String, Set<Integer>> index, ArrayList<Predicate> clause) {
		
		long startTime = System.currentTimeMillis();		
		
		ArrayList<ArrayList<Predicate>> queryList = new ArrayList<>();
		queryList.add(clause);
		
		while (!queryList.isEmpty()) {
			
			ArrayList<ArrayList<Predicate>> result = new ArrayList<>();
			
			for (ArrayList<Predicate> query : queryList) {
				
				for (int i = 0; i < query.size(); i++) { // each Predicate in query
					Predicate p = query.get(i);
					String negKey = p.name;
					if (p.positive) {
						negKey = "~" + negKey;
					}
					
					// add time...
					if ((System.currentTimeMillis() - startTime)/1000 > 10) {
						return false;
					}
					
					if (index.containsKey(negKey)) {
						Set<Integer> idxInKB = index.get(negKey);
						for (int idx : idxInKB) {
							ArrayList<Predicate> potentialPal = KB.get(idx);
							for (int j = 0; j < potentialPal.size(); j++) { // each Predicate in pal
								
								Map<String, String> theta = new HashMap<>(); // ?..I guess...
								if ((theta = resolve2(p, potentialPal.get(j), theta)) != null) { // It is a pal!
									
									ArrayList<Predicate> newClause = new ArrayList<>();// clause exclude i, pal exclude j
									
									ArrayList<Predicate> queryCopy = copyClause(query);
									queryCopy.remove(i);
									updateVar(queryCopy, theta);
									newClause.addAll(queryCopy);
									
									// shadow reference...
									ArrayList<Predicate> palCopy = copyClause(potentialPal);
									palCopy.remove(j);
									updateVar(palCopy, theta);
									newClause.addAll(palCopy);
									
									if (newClause.size() == 0) {
										return true;
									}							
									result.add(newClause);
								}
							}
						}						
					}
				}
			}
			
			
			boolean someNew = false;
			for (int i = 0; i < queryList.size(); i++) {
				ArrayList<Predicate> query = queryList.get(i);
				// add query to KB and update index
				if(addToKB(KB, index, query)) {
					someNew = true;
				}
				// add time...
				if ((System.currentTimeMillis() - startTime)/1000 > 10) {
					return false;
				}
			}
			if (!someNew) return false;
			
			queryList = result;
		}
		
		return false;
	}
	
	private static void updateVar(ArrayList<Predicate> clause, Map<String, String> theta) {
		
		for (Predicate p : clause) {
			ArrayList<String> arguments = p.arguments;
			for (int i = 0; i < arguments.size(); i++) {
				
				String key = arguments.get(i);
				if (theta.containsKey(key)) {
					arguments.set(i, theta.get(key));
				}
//				while (theta.containsKey(key)) {
//					key = theta.get(key);
//				}
//				arguments.set(i, key);
			}
		}
	}
	
	private static ArrayList<Predicate> copyClause(ArrayList<Predicate> clause) {
		ArrayList<Predicate> copy = new ArrayList<>();
		for (int i = 0; i < clause.size(); i++) {
			Predicate pCopy = new Predicate(clause.get(i));	
			copy.add(pCopy);
		}
		return copy;
	}
	
	private static Map<String, String> resolve2(Predicate a, Predicate b, Map<String, String> theta) {
		if (theta == null) return null;
		if ((!a.name.equals(b.name)) || (a.positive == b.positive)) return null;
		return unifyList2(a.arguments, b.arguments, theta);
	}
	
	private static Map<String, String> unifyList2(List<String> list1, List<String> list2, Map<String, String> theta) {
		if (theta == null) return null;
		if (list1.size() != list2.size()) return null;
		
		String s1 = list1.get(0);
		String s2 = list2.get(0);

		if (list1.size() == 1 && list2.size() == 1) {
			return unifyVar2(s1, s2, theta);
		}
		return unifyList2(list1.subList(1, list1.size()), list2.subList(1, list2.size()), unifyVar2(s1, s2, theta));
	}
	
	// PRE: theta is updated...
	private static Map<String, String> unifyVar2(String s1, String s2, Map<String, String> theta) {
		if (theta == null) return null;
		
		if (theta.containsKey(s1)) {
			s1 = theta.get(s1);
		} else if (theta.containsKey(s2)) {
			s2 = theta.get(s2);
		} // s2 is ground (not key)
		
		if (!isVariable(s1) && !isVariable(s2)) { // maybe switch to Constant before...
			if (!s1.equals(s2)) {
				return null;
			}
			return theta;
		}
		
		if (!isVariable(s1)) {
			String tmp = s1;
			s1 = s2;
			s2 = tmp;
		} // s1 is var
		
		theta.put(s1, s2);
		return theta;
	}	

}
