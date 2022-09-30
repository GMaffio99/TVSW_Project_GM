package mortal_chess_tests;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

import junitparams.JUnitParamsRunner;
import mortal_chess.Attaccante;
import mortal_chess.AttaccanteDifensore;
import mortal_chess.Difensore;
import mortal_chess.Pedina;
import mortal_chess.Tavolo;

@RunWith(JUnitParamsRunner.class)
public class TavoloTest {

	static Tavolo tavolo;
	
	@BeforeClass
	public static void setupTavolo() {
		tavolo = Tavolo.getTavolo();
	}
	
	@Before
	public void resetTavolo() {
		tavolo.reset();
	}
	
	@Test
	public void testGetTavolo() {
		assertNotNull(Tavolo.getTavolo());
	}

	@Test
	public void testGetListaPedineAndReset() {
		assertTrue(tavolo.getListaPedine().isEmpty());
		tavolo.getListaPedine().put(0, null);
		assertFalse(tavolo.getListaPedine().isEmpty());
		tavolo.reset();
		assertTrue(tavolo.getListaPedine().isEmpty());
	}

	@Test
	public void testSetPuntiAndGetPuntiGiocatore() {
		assertEquals(tavolo.getPuntiGiocatoreX(), 10);
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		tavolo.setPuntiGiocatoreX(3);
		tavolo.setPuntiGiocatoreO(2);
		assertEquals(tavolo.getPuntiGiocatoreX(), 3);
		assertEquals(tavolo.getPuntiGiocatoreO(), 2);
		tavolo.setPunti(5);
		assertEquals(tavolo.getPuntiGiocatoreX(), 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
	}

	@Test
	public void testPartitaFinitaAndGetVincitore() {
		assertFalse(tavolo.partitaFinita());
		assertEquals(tavolo.getVincitore(), '-');
		tavolo.setPuntiGiocatoreX(0);
		assertTrue(tavolo.partitaFinita());
		assertEquals(tavolo.getVincitore(), 'O');
		tavolo.setPuntiGiocatoreX(1);
		tavolo.setPuntiGiocatoreO(0);
		assertTrue(tavolo.partitaFinita());
		assertEquals(tavolo.getVincitore(), 'X');
	}
	
	@Test
	public void testGetPedina() {
		assertNull(tavolo.getPedina('1', 'A'));
		assertNull(tavolo.getPedina(1, 'A'));
		Pedina p = new Attaccante('X', 1, 'A');
		tavolo.getListaPedine().put(0, p);
		assertNotNull(tavolo.getPedina('1', 'A'));
		assertNotNull(tavolo.getPedina(1,  'A'));
		Pedina p2 = tavolo.getPedina(1,  'A');
		assertEquals(p2.getGiocatore(), 'X');
		assertEquals(p2.getRiga(), 1);
		assertEquals(p2.getColonna(), 'A');
		assertTrue(p2 instanceof Attaccante);
		Attaccante a = (Attaccante) p2;
		assertEquals(a.getPuntiAttacco(), 1);
	}

	@Test
	public void testMossaEseguibileMCDC() {
		
//		int cont = 0;
//	1	switch (mossa) {
//
//		case '1': {
//			char colonna = giocatore == 'X' ? 'A' : 'H';
//			for (Pedina p: listaPedine.values()) {
//	2			if (p.getGiocatore() == giocatore && p.getColonna() == colonna)
//					cont++;
//			}
//	3		if (cont < 8)
//				return true;
//			System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Tutte le celle della colonna " + colonna + " sono occupate");
//			break;
//		}
//
//		case '2': {
//			for (Pedina p: listaPedine.values()) {
//	4			if (p.getGiocatore() == giocatore) {
//					cont++;
//	5				if (pedinaMovibile(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
//						return true;
//				}
//			}
//	6		if (cont > 0)
//				System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessuna pedina del giocatore " + giocatore + " può essere mossa");	
//			break;
//		}
//
//		case '3': {
//			for (Pedina p: listaPedine.values()) {
//	7			if (p.getGiocatore() == giocatore) {
//					cont++;
//	8				if (pedinaUnibile(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
//						return true;
//				}
//			}
//	9		if (cont > 0)
//				System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessuna pedina del giocatore " + giocatore + " può essere unita");
//			break;
//		}
//
//		case '4': {
//			int contAttaccanti = 0;
//			for (Pedina p: listaPedine.values()) {
//	10			if (p.getGiocatore() == giocatore) {
//					cont++;
//	11				if (p.isAttaccante()) {
//						contAttaccanti++;
//	12					if (pedinaAttaccante(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
//							return true;
//					}
//				}
//			}
//	13		if (cont > 0) {
//	14			if (contAttaccanti == 0)
//					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha attaccanti");
//				else
//					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessun attaccante del giocatore " + giocatore + " può attaccare");
//			}
//			break;
//		}
//
//		case '5': {
//			int contAttaccanti = 0;
//			for (Pedina p: listaPedine.values()) {
//	15			if (p.getGiocatore() == giocatore) {
//					cont++;
//	16				if (p.isAttaccante()) {
//						contAttaccanti++;
//	17					if (pedinaAttaccanteAvversario(giocatore, intToChar(p.getRiga()), p.getColonna()) == 0)
//							return true;
//					}
//				}
//			}
//	18		if (cont > 0) {
//	19			if (contAttaccanti == 0)
//					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha attaccanti");
//				else
//					System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Nessun attaccante del giocatore " + giocatore + " può attaccare");
//			}
//			break;
//		}
//		
//		default: return false;
//		
//		}
//	20	if (cont == 0)
//			System.out.println("[" + giocatore + "]" + " MOSSA NON ESEGUIBILE! Il giocatore " + giocatore + " non ha pedine schierate");
//		return false;
//	}
		
		
		
		/* TC1
		 * mossa 0 non valida
		 * decisione 1 : case default
		 */
		assertFalse(tavolo.mossaEseguibile('0', 'X'));
		
		/* TC2
		 * mossa 1 eseguibile - almeno una cella libera nella prima colonna
		 * decisione 1 : case '1'
		 * decisione 2 : T && T ---> T
		 * decisione 2 : T && F ---> F
		 * decisione 2 : F && T ---> F
		 * decisione 3 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A'); // decisione 2 : T && T ---> T
		tavolo.posizionaPedina('X', 'A', '1', 'B'); // decisione 2 : T && F ---> F
		tavolo.posizionaPedina('O', 'A', '1', 'H'); // decisione 2 : F && T ---> F
		assertTrue(tavolo.mossaEseguibile('1', 'X'));
		
		/* TC3
		 * mossa 1 non eseguibile - nessuna cella libera nella prima colonna
		 * decisione 1 : case '1'
		 * decisione 2 : T && T ---> T
		 * decisione 3 : F
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		tavolo.posizionaPedina('X', 'A', '3', 'A');
		tavolo.posizionaPedina('X', 'A', '4', 'A');
		tavolo.posizionaPedina('X', 'A', '5', 'A');
		tavolo.posizionaPedina('X', 'A', '6', 'A');
		tavolo.posizionaPedina('X', 'A', '7', 'A');
		tavolo.posizionaPedina('X', 'A', '8', 'A');
		assertFalse(tavolo.mossaEseguibile('1', 'X'));
		
		/* TC4
		 * mossa 2 eseguibile - almeno una pedina movibile
		 * decisione 1 : case '2'
		 * decisione 4 : T
		 * decisione 5 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A'); // D4:T - D5:T
		assertTrue(tavolo.mossaEseguibile('2', 'X'));
		
		/* TC5
		 * mossa 2 non eseguibile - nessuna pedina movibile
		 * decisione 1 : case '2'
		 * decisione 4 : T
		 * decisione 4 : F
		 * decisione 5 : F
		 * decisione 6 : T
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '2', 'A');
		tavolo.posizionaPedina('O', 'A', '1', 'B');
		tavolo.posizionaPedina('O', 'A', '2', 'B');
		assertFalse(tavolo.mossaEseguibile('2', 'X'));
		
		/* TC6
		 * mossa 2 non eseguibile - nessuna pedina schierata
		 * decisione 1 : case '2'
		 * decisione 6 : F
		 * decisione 20 : T
		 */
		tavolo.reset();
		assertFalse(tavolo.mossaEseguibile('2', 'X'));
		
		/* TC7
		 * mossa 3 eseguibile - almeno una pedina unibile
		 * decisione 1 : case '3'
		 * decisione 7 : T
		 * decisione 8 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '1', 'B');
		assertTrue(tavolo.mossaEseguibile('3', 'X'));
		
		/* TC8
		 * mossa 3 non eseguibile - nessuna pedina unibile
		 * decisione 1 : case '3'
		 * decisione 7 : T
		 * decisione 8 : F
		 * decisione 9 : T
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '3', 'A');
		assertFalse(tavolo.mossaEseguibile('3', 'X'));
		
		/* TC9
		 * mossa 3 non eseguibile - nessuna pedina schierata
		 * decisione 1 : case '3'
		 * decisione 7 : F
		 * decisione 9 : F
		 * decisione 20 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('O', 'A', '1', 'H');
		assertFalse(tavolo.mossaEseguibile('3', 'X'));
		
		/* TC10
		 * mossa 4 eseguibile - almeno una pedina può attaccare una pedina
		 * decisione 1 : case '4'
		 * decisione 10 : T
		 * decisione 11 : T
		 * decisione 12 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '1', 'B');
		assertTrue(tavolo.mossaEseguibile('4', 'X'));
		
		/* TC11
		 * mossa 4 non eseguibile - nessuna pedina può attaccare una pedina
		 * decisione 1 : case '4'
		 * decisione 10 : T
		 * decisione 11 : T
		 * decisione 12 : F
		 * decisione 13 : T
		 * decisione 14 : F
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertFalse(tavolo.mossaEseguibile('4', 'X'));
		
		/* TC12
		 * mossa 4 non eseguibile - nessuna pedina attaccante
		 * decisione 1 : case '4'
		 * decisione 10 : T
		 * decisione 11 : F
		 * decisione 13 : T
		 * decisione 14 : T
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'D', '1', 'A');
		assertFalse(tavolo.mossaEseguibile('4', 'X'));
		
		/* TC13
		 * mossa 4 non eseguibile - nessuna pedina schierata
		 * decisione 1 : case '4'
		 * decisione 10 : F
		 * decisione 13 : F
		 * decisione 20 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('O', 'D', '1', 'H');
		assertFalse(tavolo.mossaEseguibile('4', 'X'));
		
		/* TC14
		 * mossa 5 eseguibile - almeno una pedina può attaccare l'avversario
		 * decisione 1 : case '5'
		 * decisione 15 : T
		 * decisione 16 : T
		 * decisione 17 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'H');
		assertTrue(tavolo.mossaEseguibile('5', 'X'));
		
		/* TC15
		 * mossa 5 non eseguibile - nessuna pedina può attaccare l'avversario
		 * decisione 1 : case '5'
		 * decisione 15 : T
		 * decisione 16 : T
		 * decisione 17 : F
		 * decisione 18 : T
		 * decisione 19 : F
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertFalse(tavolo.mossaEseguibile('5', 'X'));
		
		/* TC16
		 * mossa 5 non eseguibile - nessuna pedina attaccante
		 * decisione 1 : case '5'
		 * decisione 15 : T
		 * decisione 16 : F
		 * decisione 18 : T
		 * decisione 19 : T
		 * decisione 20 : F
		 */
		tavolo.reset();
		tavolo.posizionaPedina('X', 'D', '1', 'H');
		assertFalse(tavolo.mossaEseguibile('5', 'X'));
		
		/* TC17
		 * mossa 5 non eseguibile - nessuna pedina schierata
		 * decisione 1 : case '5'
		 * decisione 15 : F
		 * decisione 18 : F
		 * decisione 20 : T
		 */
		tavolo.reset();
		tavolo.posizionaPedina('O', 'D', '1', 'H');
		assertFalse(tavolo.mossaEseguibile('5', 'X'));
		
	}

	@Test
	public void testCellaOccupata() {
		assertFalse(tavolo.cellaOccupata('1', 'A'));
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertTrue(tavolo.cellaOccupata('1', 'A'));
	}

	@Test
	public void testPosizionaPedina() {
		tavolo.posizionaPedina('O', 'D', '2', 'B');
		Pedina p = tavolo.getPedina('2', 'B');
		assertEquals(p.getGiocatore(), 'O');
		assertEquals(p.getRiga(), 2);
		assertEquals(p.getColonna(), 'B');
		assertTrue(p instanceof Difensore);
		Difensore d = (Difensore) p;
		assertEquals(d.getPuntiDifesa(), 1);
	}

	@Test
	public void testPedinaMovibile() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaMovibile('O', '1', 'A'), -1);
		// return 0 - pedina movibile
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 0);
		// return 1 - pedina non movibile per celle adiacenti occupate
		tavolo.posizionaPedina('X', 'A', '1', 'B');
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		tavolo.posizionaPedina('X', 'A', '2', 'B');
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 1);
	}

	@Test
	public void testCellaRaggiungibile() {
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		// return -1 - cella non raggiungibile perchè non adiacente
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '3', 'A'), -1);
		// return 1 - cella non raggiungibile perchè occupata
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '2', 'A'), 1);
		// return 0 - cella raggiungibile
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '1', 'B'), 0);
	}

	@Test
	public void testMuoviPedina() {
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.getListaPedine().get(0).getRiga(), 1);
		assertEquals(tavolo.getListaPedine().get(0).getColonna(), 'A');
		Pedina p = new Attaccante('X', 1, 'A');
		assertTrue(tavolo.getListaPedine().get(0).equals(p));
		
		tavolo.muoviPedina('1', 'A', '2', 'B');
		assertNull(tavolo.getListaPedine().get(0));
		assertEquals(tavolo.getListaPedine().get(9).getRiga(), 2);
		assertEquals(tavolo.getListaPedine().get(9).getColonna(), 'B');
		assertFalse(tavolo.getListaPedine().get(9).equals(p));
	}

	@Test
	public void testPedinaUnibile() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaUnibile('O', '1', 'A'), -1);
		// return 1 - nessuna pedina adiacente da poter unire
		tavolo.posizionaPedina('O', 'A', '1', 'B');
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 1);
		// return 0 - pedina unibile
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 0);
	}

	@Test
	public void testPedineUnibili() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedineUnibili('X', '1', 'A', '2', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		assertEquals(tavolo.pedineUnibili('O', '1', 'A', '2', 'A'), -1);
		// return 1 - pedine non adiacenti
		assertEquals(tavolo.pedineUnibili('X', '1', 'H', '2', 'A'), 1);
		// return 0 - pedine unibili
		assertEquals(tavolo.pedineUnibili('X', '1', 'A', '2', 'A'), 0);
	}

	@Test
	public void testUnisciPedine() {
		Pedina p1 = new Attaccante('X', 1, 'A');
		Pedina p2 = new Difensore('X', 2, 'A');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertNotNull(tavolo.getListaPedine().get(0));
		assertTrue(tavolo.getListaPedine().get(0).equals(p1));
		assertNotNull(tavolo.getListaPedine().get(8));
		assertTrue(tavolo.getListaPedine().get(8).equals(p2));
		
		Pedina p3 = new AttaccanteDifensore('X', 1, 'A', 1, 1);
		tavolo.unisciPedine('1', 'A', '2', 'A');
		assertNotNull(tavolo.getListaPedine().get(0));
		assertTrue(tavolo.getListaPedine().get(0).equals(p3));
		assertNull(tavolo.getListaPedine().get(8));
	}

	@Test
	public void testPedinaAttaccante() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 2);
		// return -1 - pedina appartenente all'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaAttaccante('O', '1', 'A'), -1);
		// return 3 - pedina non attaccante
		tavolo.posizionaPedina('X', 'D', '1', 'H');
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'H'), 3);
		// return 1 - pedina non ha avversari adiacenti
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 1);
		// return 0 - pedina può attaccare
		tavolo.posizionaPedina('O', 'D', '1', 'B');
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 0);
	}

	@Test
	public void testPedinaAttaccabile() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'B'), 2);
		// return -1 - pedina da attaccare non appartenente all'avversario
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '2', 'A'), -1);
		// return 1 - pedina da attaccare non adiacente
		tavolo.posizionaPedina('O', 'D', '1', 'H');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'H'), 1);
		// return 0 - pedina attaccabile
		tavolo.posizionaPedina('O', 'D', '1', 'B');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'B'), 0);
	}

	@Test
	public void testAttaccaPedina() {
		// pedina attaccante AD non esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.getListaPedine().put(0, new AttaccanteDifensore('X', 1, 'A', 2, 1));
		tavolo.getListaPedine().put(1, new Difensore('O', 1, 'B', 3));
		tavolo.attaccaPedina('1', 'A', '1', 'B');
		AttaccanteDifensore ad = (AttaccanteDifensore) tavolo.getListaPedine().get(0);
		assertEquals(ad.getPuntiAttacco(), 1);
		Difensore d = (Difensore) tavolo.getListaPedine().get(1);
		assertNotNull(d);
		assertEquals(d.getPuntiDifesa(), 1);
		// pedina attaccante AD esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.attaccaPedina('1', 'A', '1', 'B');
		Pedina p = tavolo.getListaPedine().get(0);
		assertTrue(p instanceof Difensore);
		assertNull(tavolo.getListaPedine().get(1));
		// pedina attaccante A non esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.getListaPedine().put(63, new Attaccante('O', 8, 'H', 2));
		tavolo.getListaPedine().put(55, new Difensore('X', 7, 'H', 3));
		tavolo.attaccaPedina('8', 'H', '7', 'H');
		Attaccante a = (Attaccante) tavolo.getListaPedine().get(63);
		assertEquals(a.getPuntiAttacco(), 1);
		d = (Difensore) tavolo.getListaPedine().get(55);
		assertNotNull(d);
		assertEquals(d.getPuntiDifesa(), 1);
		// pedina attaccante A esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.attaccaPedina('8', 'H', '7', 'H');
		assertNull(tavolo.getListaPedine().get(63));
		assertNull(tavolo.getListaPedine().get(55));
	}

	@Test
	public void testPedinaAttaccanteAvversario() {
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'H'), 2);
		// return -1 - pedina appartenente all'avversario
		tavolo.posizionaPedina('O', 'A', '1', 'A');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'A'), -1);
		// return 3 - pedina non attaccante
		tavolo.posizionaPedina('X', 'D', '8', 'H');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '8', 'H'), 3);
		// return 1 - pedina non può attaccare l'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'G');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'G'), 1);
		tavolo.posizionaPedina('O', 'A', '8', 'B');
		assertEquals(tavolo.pedinaAttaccanteAvversario('O', '8', 'B'), 1);
		// return 0 - pedina può attaccare l'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'H');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'H'), 0);
		assertEquals(tavolo.pedinaAttaccanteAvversario('O', '1', 'A'), 0);
	}

	@Test
	public void testAttaccaAvversario() {
		// pedina attaccante AD non esaurisce punti attacco
		tavolo.getListaPedine().put(7, new AttaccanteDifensore('X', 1, 'H', 2, 1));
		tavolo.attaccaAvversario('X', '1', 'H');
		AttaccanteDifensore ad = (AttaccanteDifensore) tavolo.getListaPedine().get(7);
		assertEquals(ad.getPuntiAttacco(), 1);
		assertEquals(tavolo.getPuntiGiocatoreO(), 8);
		// pedina attaccante AD esaurisce punti attacco
		tavolo.attaccaAvversario('X', '1', 'H');
		Pedina p = tavolo.getListaPedine().get(7);
		assertTrue(p instanceof Difensore);
		assertEquals(tavolo.getPuntiGiocatoreO(), 7);
		// pedina attaccante A non esaurisce punti attacco
		tavolo.getListaPedine().put(56, new Attaccante('O', 8, 'A', 2));
		tavolo.attaccaAvversario('O', '8', 'A');
		Attaccante a = (Attaccante) tavolo.getListaPedine().get(56);
		assertEquals(a.getPuntiAttacco(), 1);
		assertEquals(tavolo.getPuntiGiocatoreX(), 8);
		// pedina attaccante A esaurisce punti attacco
		tavolo.attaccaAvversario('O', '8', 'A');
		assertNull(tavolo.getListaPedine().get(56));
		assertEquals(tavolo.getPuntiGiocatoreX(), 7);
	}

	@Test
	public void testDiminuisciPuntiGiocatore() {
		assertEquals(tavolo.getPuntiGiocatoreX(), 10);
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		tavolo.diminuisciPuntiGiocatore('X', 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
		tavolo.diminuisciPuntiGiocatore('O', 7);
		assertEquals(tavolo.getPuntiGiocatoreX(), 3);
	}

}
