package mortal_chess;

import java.util.ArrayList;

public final class TavoloUtils {
	
	//@ requires s != null && s.length() > 0;
		public static boolean isInteger(String s) { 
			try {  
				Integer.parseInt(s);  
				return true;
			} catch(NumberFormatException e){  
				return false;  
			}
		}
	
	/*@ requires c >= '1' && c <= '8';
	  @ ensures \result == 1 <==> c == '1';
	  @ ensures \result == 2 <==> c == '2';
	  @ ensures \result == 3 <==> c == '3';
	  @ ensures \result == 4 <==> c == '4';
	  @ ensures \result == 5 <==> c == '5';
	  @ ensures \result == 6 <==> c == '6';
	  @ ensures \result == 7 <==> c == '7';
	  @ ensures \result == 8 <==> c == '8';
	  @*/
	public static int charToInt(char c) {
		switch (c) {
			case '1': return 1; 
			case '2': return 2;
			case '3': return 3;
			case '4': return 4;
			case '5': return 5;
			case '6': return 6;
			case '7': return 7;
			case '8': return 8;
			default: return 0;
		}
	}
	
	/*@ requires i >= 1 && i <= 8;
	  @ ensures \result == '1' <==> i == 1;
	  @ ensures \result == '2' <==> i == 2;
	  @ ensures \result == '3' <==> i == 3;
	  @ ensures \result == '4' <==> i == 4;
	  @ ensures \result == '5' <==> i == 5;
	  @ ensures \result == '6' <==> i == 6;
	  @ ensures \result == '7' <==> i == 7;
	  @ ensures \result == '8' <==> i == 8;
	  @*/
	public static char intToChar(int i) {
		switch(i) {
			case 1: return '1'; 
			case 2: return '2';
			case 3: return '3';
			case 4: return '4';
			case 5: return '5';
			case 6: return '6';
			case 7: return '7';
			case 8: return '8';
			default: return '0';
		}
	}
	
	//@ pure
	public static int getIndex(char riga, char colonna) {
		return getIndex(charToInt(riga), colonna);
	}
	
	/*@ requires riga >= 1 && riga <= 8;
	  @ requires colonna >= 'A' && colonna <= 'H';
	  @ ensures \result == (8 * (riga-1) + 0) <==> colonna == 'A';
	  @ ensures \result == (8 * (riga-1) + 1) <==> colonna == 'B';
	  @ ensures \result == (8 * (riga-1) + 2) <==> colonna == 'C';
	  @ ensures \result == (8 * (riga-1) + 3) <==> colonna == 'D';
	  @ ensures \result == (8 * (riga-1) + 4) <==> colonna == 'E';
	  @ ensures \result == (8 * (riga-1) + 5) <==> colonna == 'F';
	  @ ensures \result == (8 * (riga-1) + 6) <==> colonna == 'G';
	  @ ensures \result == (8 * (riga-1) + 7) <==> colonna == 'H';
	  @ pure
	  @*/
	public static int getIndex(int riga, char colonna) {
		int col;
		switch (colonna) {
			case 'A': col = 0; break;
			case 'B': col = 1; break;
			case 'C': col = 2; break;
			case 'D': col = 3; break;
			case 'E': col = 4; break;
			case 'F': col = 5; break;
			case 'G': col = 6; break;
			case 'H': col = 7; break;
			default: return -1;
		}
		return 8 * (riga-1) + col;
	}
	
	/*@ requires riga >= 1 && riga <= 8;
	  @ requires colonna >= 'A' && colonna <= 'H';
	  @ ensures \result != null && !(\result.isEmpty());
	  @*/
	public static ArrayList<Coppia<Integer, Character>> getCelleAdiacenti(char riga, char colonna, boolean ad) {
		int r = charToInt(riga);
		ArrayList<Coppia<Integer, Character>> result = new ArrayList<Coppia<Integer, Character>>();
		if (colonna != 'A') {
			char letteraPrecedente = 'x';
			switch (colonna) {
				case 'B': letteraPrecedente = 'A'; break;
				case 'C': letteraPrecedente = 'B'; break;
				case 'D': letteraPrecedente = 'C'; break;
				case 'E': letteraPrecedente = 'D'; break;
				case 'F': letteraPrecedente = 'E'; break;
				case 'G': letteraPrecedente = 'F'; break;
				case 'H': letteraPrecedente = 'G'; break;
				default: break;
			}
			if (r != 1 && !ad) result.add(new Coppia<Integer, Character>(r-1, letteraPrecedente));
			result.add(new Coppia<Integer, Character>(r, letteraPrecedente));
			if (r != 8 && !ad) result.add(new Coppia<Integer, Character>(r+1, letteraPrecedente));
		}
		if (r != 1) result.add(new Coppia<Integer, Character>(r-1, colonna));
		if (r != 8) result.add(new Coppia<Integer, Character>(r+1, colonna));
		if (colonna != 'H') {
			char letteraSuccessiva = 'x';
			switch (colonna) {
				case 'A': letteraSuccessiva = 'B'; break;
				case 'B': letteraSuccessiva = 'C'; break;
				case 'C': letteraSuccessiva = 'D'; break;
				case 'D': letteraSuccessiva = 'E'; break;
				case 'E': letteraSuccessiva = 'F'; break;
				case 'F': letteraSuccessiva = 'G'; break;
				case 'G': letteraSuccessiva = 'H'; break;
				default: return null;
			}
			if (r != 1 && !ad) result.add(new Coppia<Integer, Character>(r-1, letteraSuccessiva));
			result.add(new Coppia<Integer, Character>(r, letteraSuccessiva));
			if (r != 8 && !ad) result.add(new Coppia<Integer, Character>(r+1, letteraSuccessiva));
		}
		return result;
	}
	
}
