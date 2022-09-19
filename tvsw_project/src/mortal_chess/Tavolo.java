package mortal_chess;

import java.util.ArrayList;
import java.util.HashMap;


public class Tavolo {
	
	private static Tavolo tavolo;
	
	private int puntiGiocatoreX;
	private int puntiGiocatoreO;
	private HashMap<Integer, Pedina> listaPedine;

	
	private Tavolo() {
		puntiGiocatoreX = puntiGiocatoreO = 10;
		listaPedine = new HashMap<>();
	}
	
	public static Tavolo getTavolo() {
		if (tavolo == null)
			tavolo = new Tavolo();
		return tavolo;
	}
	
	public HashMap<Integer, Pedina> getListaPedine() {
		return listaPedine;
	}
	
	public void reset() {
		setPunti(10);
		listaPedine.clear();
	}
	
	public void setPuntiGiocatoreX(int p) {
		puntiGiocatoreX = p;
	}
	
	public void setPuntiGiocatoreO(int p) {
		puntiGiocatoreO = p;
	}
	
	public void setPunti(int p) {
		setPuntiGiocatoreX(p);
		setPuntiGiocatoreO(p);
	}
	
	public int getPuntiGiocatoreX() {
		return puntiGiocatoreX;
	}
	
	public int getPuntiGiocatoreO() {
		return puntiGiocatoreO;
	}
	
	public boolean partitaFinita() {
		return puntiGiocatoreX <= 0 || puntiGiocatoreO <= 0;
	}
	
	public char getVincitore() {
		return puntiGiocatoreX <= 0 ? 'O' : 'X';
	}
	
	public void print() {
		
		System.out.println("~~~ Giocatore X - Punti vita: " + puntiGiocatoreX + " ~~~");
		System.out.println("Lista pedine: ");
		
		for (Pedina p: listaPedine.values()) {
			if (p.getGiocatore() == 'X')
				System.out.println(" - " + p);
		}
		
		System.out.println();
		
		System.out.println("~~~ Giocatore O - Punti vita: " + puntiGiocatoreO + " ~~~");
		System.out.println("Lista pedine: ");
		
		for (Pedina p: listaPedine.values()) {
			if (p.getGiocatore() == 'O')
				System.out.println(" - " + p);
		}
		
		System.out.println();
		
		System.out.println("         +---+---+---+---+---+---+---+---+    ");
		System.out.println("         | A | B | C | D | E | F | G | H |    ");
		System.out.println("     +---+---+---+---+---+---+---+---+---+---+");
		
		char[] colonne = {'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'};
		for (int riga = 1; riga <= 8; riga++) {
			System.out.print("     | " + riga + " |");
			for (int colonna = 0; colonna < 8; colonna++) {
				Pedina p = getPedina(riga, colonne[colonna]);
				if (p != null)
					System.out.print(" " + p.getGiocatore() + " |");
				else
					System.out.print("   |");
			}
			System.out.println(" " + riga + " |");
			System.out.println("     +---+---+---+---+---+---+---+---+---+---+");
		}
		
		System.out.println("         | A | B | C | D | E | F | G | H |    ");
		System.out.println("         +---+---+---+---+---+---+---+---+    ");
		System.out.println();
		
	}
	
	
	public int charToInt(char c) {
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
	
	public char intToChar(int i) {
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
	
	public int getIndex(char riga, char colonna) {
		return getIndex(charToInt(riga), colonna);
	}
	
	public int getIndex(int riga, char colonna) {
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
			default: col = -1; break;
		}
		return 8 * (riga-1) + col;
	}
	
	public Pedina getPedina(char riga, char colonna) {
		return getPedina(charToInt(riga), colonna);
	}
	
	public Pedina getPedina(int riga, char colonna) {
		Pedina p = listaPedine.get(getIndex(riga, colonna));
		if (p == null)
			return null;
		return p;
	}
	
	
	public boolean mossaEseguibile(char mossa, char giocatore) {
		
		if (mossa != '1' && mossa != '2' && mossa != '3' && mossa != '4' && mossa != '5')
			return false;

		int cont = 0;

		switch (mossa) {

		case '1': {

			char colonna = giocatore == 'X' ? 'A' : 'H';
			
			for (Pedina p: listaPedine.values()) {
				if (p.getGiocatore() == giocatore && p.getColonna() == colonna)
					cont++;
			}

			if (cont < 8)
				return true;
			
			System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Tutte le celle della colonna " + colonna + " sono occupate");
			
			break;
			
		}

		case '2': {
			
			for (Pedina p: listaPedine.values()) {
				if (p.getGiocatore() == giocatore) {
					cont++;
					if (pedinaMovibile(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
						return true;
				}
			}

			if (cont > 0)
				System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessuna pedina del giocatore " + giocatore + " può essere mossa");
				
			break;
		}

		case '3': {
			
			for (Pedina p: listaPedine.values()) {
				if (p.getGiocatore() == giocatore) {
					cont++;
					if (pedinaUnibile(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
						return true;
				}
			}

			if (cont > 0)
				System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessuna pedina del giocatore " + giocatore + " può essere unita");
			
			break;
		}

		case '4': {

			int contAttaccanti = 0;

			for (Pedina p: listaPedine.values()) {
				if (p.getGiocatore() == giocatore) {
					cont++;
					if (p.isAttaccante()) {
						contAttaccanti++;
						if (pedinaAttaccante(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
							return true;
					}
				}
			}

			if (cont > 0) {
				if (contAttaccanti == 0)
					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha attaccanti");
				else
					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessun attaccante del giocatore " + giocatore + " può attaccare");
			}

			break;
		}

		case '5': {

			int contAttaccanti = 0;
			
			for (Pedina p: listaPedine.values()) {
				if (p.getGiocatore() == giocatore) {
					cont++;
					if (p.isAttaccante()) {
						contAttaccanti++;
						if (pedinaAttaccanteAvversario(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
							return true;
					}
				}
			}

			if (cont > 0) {
				if (contAttaccanti == 0)
					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha attaccanti");
				else
					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessun attaccante del giocatore " + giocatore + " può attaccare");
			}

			break;
		}

		}

		if (cont == 0)
			System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha pedine schierate");

		return false;
		
	}
	
	
	public boolean cellaOccupata(char riga, char colonna) {
		return getPedina(riga, colonna) != null;
	}
	
	
	public void posizionaPedina(char giocatore, char tipologia, char riga, char colonna) {
		Pedina p;
		if (tipologia == 'A')
			p = new Attaccante(giocatore, charToInt(riga), colonna);
		else
			p = new Difensore(giocatore, charToInt(riga), colonna);
		listaPedine.put(getIndex(riga, colonna),  p);
		System.out.println("[" + giocatore + "]" + " LA PEDINA E' STATA POSIZIONATA NELLA CELLA " + colonna + riga);
		System.out.println("[" + giocatore + "]" + " " + p);
	}
	
	public ArrayList<Coppia<Integer, Character>> getCelleAdiacenti(char riga, char colonna, boolean ad) {
		int r = charToInt(riga);
		ArrayList<Coppia<Integer, Character>> result = new ArrayList<>();
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
			}
			if (r != 1 && !ad) result.add(new Coppia<Integer, Character>(r-1, letteraSuccessiva));
			result.add(new Coppia<Integer, Character>(r, letteraSuccessiva));
			if (r != 8 && !ad) result.add(new Coppia<Integer, Character>(r+1, letteraSuccessiva));
		}
		return result;
	}
	
	
	public int pedinaMovibile(char giocatore, char riga, char colonna) {
		Pedina p = getPedina(riga, colonna);
		if (p == null)
			return 2;
		if (p.getGiocatore() != giocatore)
			return -1;
		boolean ad = p.isAttaccanteDifensore();
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga, colonna, ad);
		for (Coppia<Integer, Character> c: celleAdiacenti) {
			if (getPedina(c.getPrimo(), c.getSecondo()) == null)
				return 0;
		}
		return 1;
	}
	
	public int cellaRaggiungibile(char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p = getPedina(riga1, colonna1);
		boolean ad = p.isAttaccanteDifensore();
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga1, colonna1, ad);
		if (!celleAdiacenti.contains(new Coppia<Integer, Character>(charToInt(riga2), colonna2)))
			return -1;
		if (getPedina(riga2, colonna2) != null)
			return 1;
		return 0;
	}
	
	public void muoviPedina(char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p = getPedina(riga1, colonna1);
		p.muovi(charToInt(riga2), colonna2);
		listaPedine.remove(getIndex(riga1, colonna1));
		listaPedine.put(getIndex(riga2, colonna2), p);
		System.out.println("[" + p.getGiocatore() + "]" + " LA PEDINA E' STATA MOSSA DALLA CELLA " + colonna1 + riga1 + " ALLA CELLA " + colonna2 + riga2);
		System.out.println("[" + p.getGiocatore() + "]" + " " + p);
	}
	
	public int pedinaUnibile(char giocatore, char riga, char colonna) {
		Pedina p = getPedina(riga, colonna);
		if (p == null)
			return 2;
		if (p.getGiocatore() != giocatore)
			return -1;
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga, colonna, true);
		for (Coppia<Integer, Character> c: celleAdiacenti) {
			Pedina p2 = getPedina(c.getPrimo(), c.getSecondo());
			if (p2 != null && p2.getGiocatore() == p.getGiocatore()) {
				return 0;
			}
		}
		return 1;
	}
	
	public int pedineUnibili(char giocatore, char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p2 = getPedina(riga2, colonna2);
		if (p2 == null)
			return 2;
		if (p2.getGiocatore() != giocatore)
			return -1;
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga1, colonna1, true);
		if (!celleAdiacenti.contains(new Coppia<Integer, Character>(charToInt(riga2), colonna2)))
			return 1;
		return 0;
	}
	
	public void unisciPedine(char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p1 = getPedina(riga1, colonna1);
		Pedina p2 = getPedina(riga2, colonna2);
		Pedina p = p1.unisci(p2);
		listaPedine.replace(getIndex(riga1, colonna1), p);
		listaPedine.remove(getIndex(riga2, colonna2));
		System.out.println("[" + p.getGiocatore() + "]" + " LE PEDINE NELLE CELLE " + colonna1 + riga1 + " E " + colonna2 + riga2 + " SONO STATE UNITE");
		System.out.println("[" + p.getGiocatore() + "]" + " " + p);
	}
	
	
	public int pedinaAttaccante(char giocatore, char riga, char colonna) {
		Pedina p = getPedina(riga, colonna);
		if (p == null)
			return 2;
		if (p.getGiocatore() != giocatore)
			return -1;
		if (!p.isAttaccante())
			return 3;
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga, colonna, true);
		for (Coppia<Integer, Character> c: celleAdiacenti) {
			Pedina p2 = getPedina(c.getPrimo(), c.getSecondo());
			if (p2 != null && p2.getGiocatore() != giocatore)
				return 0;
		}
		return 1;
	}
	
	public int pedinaAttaccabile(char giocatore, char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p = getPedina(riga2, colonna2);
		if (p == null)
			return 2;
		if (p.getGiocatore() == giocatore)
			return -1;
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = getCelleAdiacenti(riga1, colonna1, true);
		if (!celleAdiacenti.contains(new Coppia<Integer, Character>(charToInt(riga2), colonna2)))
			return 1;
		return 0;
	}
	
	public void attaccaPedina(char riga1, char colonna1, char riga2, char colonna2) {
		Pedina p1 = getPedina(riga1, colonna1);
		Pedina p2 = getPedina(riga2, colonna2);
		System.out.println("[" + p1.getGiocatore() + "]" + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " ATTACCA LA PEDINA NELLA CELLA " + colonna2 + riga2);
		if (p1.isAttaccanteDifensore()) {
			AttaccanteDifensore ad = (AttaccanteDifensore) p1;
			if (p2.vieneAttaccata(ad.getPuntiAttacco())) {
				listaPedine.remove(getIndex(riga2, colonna2));
				System.out.println("[" + ad.getGiocatore() + "]" + " LA PEDINA ATTACCATA HA ESAURITO I SUOI PUNTI DIFESA, VIENE RIMOSSA DAL TAVOLO");
			}
			else
				System.out.println("[" + ad.getGiocatore() + "]" + " " + p2);
			if (ad.attacca()) {
				Pedina d = new Difensore(ad.getGiocatore(), ad.getRiga(), ad.getColonna(), ad.getPuntiDifesa());
				listaPedine.replace(getIndex(riga1, colonna1), d);
				System.out.println("[" + d.getGiocatore() + "]" + " LA PEDINA ATTACCANTE-DIFENSORE HA ESAURITO I SUOI PUNTI ATTACCO, VIENE TRASFORMATA IN UNA PEDINA DIFENSORE");
				System.out.println("[" + d.getGiocatore() + "]" + " " + d);
			}
			else
				System.out.println("[" + ad.getGiocatore() + "]" + " " + ad);
		}
		else {
			Attaccante a = (Attaccante) p1;
			if (p2.vieneAttaccata(a.getPuntiAttacco())) {
				listaPedine.remove(getIndex(riga2, colonna2));
				System.out.println("[" + a.getGiocatore() + "]" + " LA PEDINA ATTACCATA HA ESAURITO I SUOI PUNTI DIFESA, VIENE RIMOSSA DAL TAVOLO");
			}
			else
				System.out.println("[" + a.getGiocatore() + "]" + " " + p2);
			if (a.attacca()) {
				listaPedine.remove(getIndex(riga1, colonna1));
				System.out.println("[" + a.getGiocatore() + "]" + " LA PEDINA ATTACCANTE HA ESAURITO I SUOI PUNTI ATTACCO, VIENE RIMOSSA DAL TAVOLO");
			}
			else
				System.out.println("[" + a.getGiocatore() + "]" + " " + a);
		}
	}
	
	
	public int pedinaAttaccanteAvversario(char giocatore, char riga, char colonna) {
		Pedina p = getPedina(riga, colonna);
		if (p == null)
			return 2;
		if (p.getGiocatore() != giocatore)
			return -1;
		if (!p.isAttaccante())
			return 3;
		if ((giocatore == 'X' && colonna != 'H') || (giocatore == 'O' && colonna != 'A'))
			return 1;
		return 0;
	}

	public void attaccaAvversario(char giocatore, char riga, char colonna) {
		Pedina p = getPedina(riga, colonna);
		if (p.isAttaccanteDifensore()) {
			AttaccanteDifensore ad = (AttaccanteDifensore) p;
			diminuisciPuntiGiocatore(giocatore, ad.getPuntiAttacco());
			if (ad.attacca()) {
				Pedina d = new Difensore(ad.getGiocatore(), ad.getRiga(), ad.getColonna(), ad.getPuntiDifesa());
				listaPedine.replace(getIndex(riga, colonna), d);
				System.out.println("[" + ad.getGiocatore() + "]" + " LA PEDINA ATTACCANTE-DIFENSORE HA ESAURITO I SUOI PUNTI ATTACCO, VIENE TRASFORMATA IN UNA PEDINA DIFENSORE");
				System.out.println("[" + ad.getGiocatore() + "]" + " " + d);
			}
			else
				System.out.println("[" + ad.getGiocatore() + "]" + " " + ad);
		}
		else {
			Attaccante a = (Attaccante) p;
			diminuisciPuntiGiocatore(giocatore, a.getPuntiAttacco());
			if (a.attacca()) {
				listaPedine.remove(getIndex(riga, colonna));
				System.out.println("[" + a.getGiocatore() + "]" + " LA PEDINA ATTACCANTE HA ESAURITO I SUOI PUNTI ATTACCO, VIENE RIMOSSA DAL TAVOLO");
			}
			else
				System.out.println("[" + a.getGiocatore() + "]" + " " + a);
		}
	}
	

	public void diminuisciPuntiGiocatore(char giocatore, int punti) {
		if (giocatore == 'X')
			setPuntiGiocatoreO(getPuntiGiocatoreO() - punti);
		else
			setPuntiGiocatoreX(getPuntiGiocatoreX() - punti);
	}
		
}
