// Haptics-Video transmission by each STA in separate ACs with video frame generation happening at 60Hz.
// With RTS-CTS exchange; expect collisions to be shorter.
// Heterogeneous modes; disabling video frames in SU mode and tx. only during UL-OFDMA
// Video frames sampled at 60 Hz but with variable frame sizes amounting to long-term avg video rate of 9.08Mbps
// Instead of frame padding in UL-OFDMA, send haptic frames

// Commands for synchronizing with Github
// git add 80211ax-TI-OFDMA-Win
// git commit -m "comment"
// git push TI-WiFi
// git status

// Jupyter notebook
// cd Documents/Git-Fresh/Jupyter/
// virtualenv SchedulingResults/
// source SchedulingResults/bin/activate
// jupyter notebook



// slot time
// CW range
// sampling rates
// sample sizes
// RTS-CTS threshold




#include <stdio.h>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* sim_time */
#include <algorithm>    // std::min
#include <math.h>       /* ceil */
#include "ti_core.h"
#include <iostream>
#include <vector>
#include <numeric>
#include <fstream>
#include <iterator>
#include <queue>
#include <map>
#include <string>
#include <cmath>
/* run this program using the console pauser or add your own getch, system("pause") or input loop */

#define CW_MIN_HA                   31 //3
#define CW_MAX_HA                   63 // 7 AC_HA
#define CW_MIN_VI                   31 //7
#define CW_MAX_VI                   63 //15 // AC_VI
//#define AIFS_VI                     44 // AIFSN*slottime+SIFS; AIFSN=2 for AC_VO and AC_VI
#define AIFS_HA                     34 // Assuming AIFSN=1 for AC_HA
#define SIFS                     16
#define SLOT_TIME                9 // 9
//#define MAX_PPDU_DURATION_US     10000 //5484µs
#define MAX_SIMULATION_TIME_US   10000000
#define RTS_TIME   				 44
#define CTS_TIME   				 44
#define PACKET_SIZE_FWD_HA				 480 // per 1ms --> 3.84Mbps
#define PACKET_SIZE_BWD_HA				 240 // per 1ms --> 1.92Mbps
#define PACKET_SIZE_BWD_VI				 38400 // 19250 bytes for 9.08 Mbps
#define PACKET_SIZE_BWD_VI_DEV		     10000
#define STA_RTS_THRESHOLD					 10000000 // 2400 bytes
#define AP_RTS_THRESHOLD					 10000000 // 2400 bytes
#define FRAGMENT_SIZE					 800 // 1375 bytes for 9.08 Mbps
//#define FRAGMENT_THRESHOLD	24

// Sampling rates -- H: 1kHz, V: 60Hz
//  V (kB) 	H (B)     Overall DR (Mbps)
// 48.75kB	200B		   25
// 38.3kB	200B		   20
// 27.9kB	200B		   15
// 17.5kB   200B 	       10
// 7.08kB   200B	        5


#define RETRY_COUNT_HA				 4 //4
#define RETRY_COUNT_VI				 7 //7
#define HA_DURATION					1000 // us
#define VI_DURATION					16949 // us -- corresponds to 59Hz
//#define HA_RATE						1000 // us
#define VI_RATE						59 // us -- corresponds to 59Hz





using namespace std;

int m_nApAntennas = 1;
int tone, tone_dl, tone_ul;
int duration_tf = 44, duration_multi_sta_back = 44, duration_back = 44, bsrptime = 44, bsrtime = 44;
int ul_ofdma_ampdu_len=0, num_collisions, fragments_per_frame;

vector<int> access_collision_0, access_collision_1, access_collision_2, access_collision_3, access_collision_vid_0,
access_collision_vid_1;
// queue array for storing STA generated packets

std::ofstream global_file, global_buffer, lostPackFile, time_track, ofdma_track, sta_file, video_file, vid_metadata_file,
			temp_file, throughput_file, hap_delay_p_file, vid_delay_p_file, kin_delay_p_file, frag_thresh_file, config_file;


void setApAntennas(int nApAntennas) {
	m_nApAntennas = nApAntennas;
}


int m_nBfees = 0; //invalid value
void setNBeamformees(int nBfees) {
	m_nBfees = nBfees;
}


int bw2ru_size(int bw) {
	//convert bw to ru_size;
	int ru_size = 0;

	if (bw == BANDWIDTH_20MHz) ru_size = RU_SIZE_242_TONES;
	else if (bw == BANDWIDTH_40MHz) ru_size = RU_SIZE_484_TONES;
	else if (bw == BANDWIDTH_80MHz) ru_size = RU_SIZE_996_TONES;
	else if (bw == BANDWIDTH_160MHz) ru_size = RU_SIZE_2x996_TONES;
	else if (bw == BANDWIDTH_320MHz) ru_size = RU_SIZE_4x996_TONES;

	return ru_size;
}

//return the maximum supported Ressource Units (RU) as a function of the channel width
//return 0 if either the channel width or the RU size is unsupported
int getMaxRUsPerChannelWidth(int bw, int ru_size) {
	int maxRUs = 0;
	if (bw == BANDWIDTH_20MHz) {
		if (ru_size == RU_SIZE_26_TONES) maxRUs = 9;
		else if (ru_size == RU_SIZE_52_TONES) maxRUs = 4;
		else if (ru_size == RU_SIZE_106_TONES) maxRUs = 2;
		else if (ru_size == RU_SIZE_242_TONES) maxRUs = 1;
		//else unsupported ru_size
	}
	else if (bw == BANDWIDTH_40MHz) {
		if (ru_size == RU_SIZE_26_TONES) maxRUs = 18;
		else if (ru_size == RU_SIZE_52_TONES) maxRUs = 8;
		else if (ru_size == RU_SIZE_106_TONES) maxRUs = 4;
		else if (ru_size == RU_SIZE_242_TONES) maxRUs = 2;
		else if (ru_size == RU_SIZE_484_TONES) maxRUs = 1;
		//else unsupported ru_size
	}
	else if (bw == BANDWIDTH_80MHz) {
		if (ru_size == RU_SIZE_26_TONES) maxRUs = 37;
		else if (ru_size == RU_SIZE_52_TONES) maxRUs = 16;
		else if (ru_size == RU_SIZE_106_TONES) maxRUs = 8;
		else if (ru_size == RU_SIZE_242_TONES) maxRUs = 4;
		else if (ru_size == RU_SIZE_484_TONES) maxRUs = 2;
		else if (ru_size == RU_SIZE_996_TONES) maxRUs = 1;
		//else unsupported ru_size
	}
	else if (bw == BANDWIDTH_160MHz) {
		if (ru_size == RU_SIZE_26_TONES) maxRUs = 74;
		else if (ru_size == RU_SIZE_52_TONES) maxRUs = 32;
		else if (ru_size == RU_SIZE_106_TONES) maxRUs = 16;
		else if (ru_size == RU_SIZE_242_TONES) maxRUs = 8;
		else if (ru_size == RU_SIZE_484_TONES) maxRUs = 4;
		else if (ru_size == RU_SIZE_996_TONES) maxRUs = 2;
		else if (ru_size == RU_SIZE_2x996_TONES) maxRUs = 1;
		//else unsupported ru_size
	}

	else if (bw == BANDWIDTH_320MHz) {
		if (ru_size == RU_SIZE_26_TONES) maxRUs = 148;
		else if (ru_size == RU_SIZE_52_TONES) maxRUs = 64;
		else if (ru_size == RU_SIZE_106_TONES) maxRUs = 32;
		else if (ru_size == RU_SIZE_242_TONES) maxRUs = 16;
		else if (ru_size == RU_SIZE_484_TONES) maxRUs = 8;
		else if (ru_size == RU_SIZE_996_TONES) maxRUs = 4;
		else if (ru_size == RU_SIZE_2x996_TONES) maxRUs = 2;
		else if (ru_size == RU_SIZE_4x996_TONES) maxRUs = 1;
		//else unsupported ru_size
	}

	return maxRUs;
}

//returns the maximum number of MPDUs within an A-MPDU
int getOfdmaAMpduLength(int mcs, int ru_size, int max_ppdu_duration, int mpdulen) {

	double data_rate;
	int cnt = 0;


	if (mcs==6){
		if (ru_size == RU_SIZE_26_TONES) {
			data_rate = 7.9;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			data_rate = 15.9;
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			data_rate = 33.8;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			data_rate = 77.4;
		}
		else if (ru_size == RU_SIZE_484_TONES) {
			data_rate = 154.9;
		}
		else if (ru_size == RU_SIZE_996_TONES) {
			data_rate = 324.3;
		}
	}

	else if (mcs==8){
		if (ru_size == RU_SIZE_26_TONES) {
			data_rate = 10.6;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			data_rate = 21.2;
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			data_rate = 45;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			data_rate = 103.2;
		}
		else if (ru_size == RU_SIZE_484_TONES) {
			data_rate = 206.5;
		}
		else if (ru_size == RU_SIZE_996_TONES) {
			data_rate = 432.4;
		}
	}



	else if (mcs==9){
		if (ru_size == RU_SIZE_26_TONES) {
			data_rate = 11.8;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			data_rate = 23.5;
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			data_rate = 50.0;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			data_rate = 114.7;
		}
		else if (ru_size == RU_SIZE_484_TONES) {
			data_rate = 229.4;
		}
		else if (ru_size == RU_SIZE_996_TONES) {
			data_rate = 480.4;
		}
		else if (ru_size == RU_SIZE_2x996_TONES) {
			data_rate = 960.8;
		}
		else if (ru_size == RU_SIZE_4x996_TONES) {
			data_rate = 1921.6;
		}
	}

	else {
		printf("MCS_%d is not supported !\n", mcs);

		exit(0);
	}

	cnt = data_rate * (max_ppdu_duration - 40) / ((44 + mpdulen)*8); // 40 is the PHY header, and 44 is the MAC header + MPDU delimiter
	return cnt;
}

int getEdcaAMpduLength(int mcs, int bw, int max_ppdu_duration, int mpdulen) {
	int ru_size = bw2ru_size(bw);
	return getOfdmaAMpduLength(mcs, ru_size, max_ppdu_duration, mpdulen);
}

int getPpduDuration(int mcs, int ru_size, int psduLen, int bw) {
	int Nbpcs, Nsd;
	float R;
	int ppdu_duration = 0;
	int Ndbps = 0;
	if ((mcs != 6) && (mcs != 9) && (mcs != 10) && (mcs != 8)) {
		printf("MCS %d is not supported\n", mcs);
		exit(0);
	}

	if (mcs==8 && bw==80){
//		26 tones-->Nsd=24, 52 tones-->Nsd=48, 106 tones-->Nsd=102, 242 tones-->Nsd=24
//		R=5/6 for mcs=9
		Nbpcs=8;
		R=0.75;
		if (ru_size == RU_SIZE_26_TONES) {
			Nsd=24;
			Ndbps = 144;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			Nsd=48;
			Ndbps = 288; //RU-52, MCS6, 1SS (corresponds to a data rate of 15.9Mbps)
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			Nsd=102;
			Ndbps = 612;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			Nsd=234;
			Ndbps = 1404;
		}
		else if (ru_size == RU_SIZE_484_TONES) { // highest for 40MHz
			Nsd=468;
			Ndbps = 2808;
		}
		else if (ru_size == RU_SIZE_996_TONES) { //// highest for 80MHz
			Nsd=980;
			Ndbps = 5880;
		}
	}


	//	Ndbps for 40MHz channel; Ndbps=Ncbps*Nsd*R*Nss; Nss=1
	if (mcs==9 && bw==80){
//		26 tones-->Nsd=24, 52 tones-->Nsd=48, 106 tones-->Nsd=102, 242 tones-->Nsd=24
//		R=5/6 for mcs=9
		if (ru_size == RU_SIZE_26_TONES) {
			Ndbps = 160;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			Ndbps = 320; //RU-52, MCS6, 1SS (corresponds to a data rate of 15.9Mbps)
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			Ndbps = 680;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			Ndbps = 1560;
		}
		else if (ru_size == RU_SIZE_484_TONES) { // highest for 40MHz
			Ndbps = 3120;
		}
		else if (ru_size == RU_SIZE_996_TONES) { //// highest for 80MHz
			Ndbps = 6240;
		}
		else if (ru_size == RU_SIZE_2x996_TONES) { // highest for 160MHz
			Ndbps = 12480;
		}
		else if (ru_size == RU_SIZE_4x996_TONES) { // highest for 320MHz
			Ndbps = 24960;
		}
	}

	if (mcs==6 && bw==80){
		Nbpcs=6;
		R=0.75;
	//		26 tones-->Nsd=24, 52 tones-->Nsd=48, 106 tones-->Nsd=102, 242 tones-->Nsd=24
	//		R=5/6 for mcs=9
		if (ru_size == RU_SIZE_26_TONES) {
			Nsd=24;
			Ndbps = 108;
		}
		else if (ru_size == RU_SIZE_52_TONES) {
			Nsd=48;
			Ndbps = 216; //RU-52, MCS6, 1SS (corresponds to a data rate of 15.9Mbps)
		}
		else if (ru_size == RU_SIZE_106_TONES) {
			Nsd=102;
			Ndbps = 459;
		}
		else if (ru_size == RU_SIZE_242_TONES) {
			Nsd=234;
			Ndbps = 1053;
		}
		else if (ru_size == RU_SIZE_484_TONES) { // highest for 40MHz
			Nsd=468;
			Ndbps = 2106;
		}
		else if (ru_size == RU_SIZE_996_TONES) { //// highest for 80MHz
			Nsd=980;
			Ndbps = 4410;
		}
	}

//	//	Ndbps for 40MHz channel; Ndbps=Ncbps*Nsd*R*Nss; Nss=1
//	if (mcs==10){
//		// 26 tones-->Nsd=24, 52 tones-->Nsd=48, 106 tones-->Nsd=102, 242 tones-->Nsd=234, 484 tones-->Nsd=468
//		// R=3/4 for mcs=10
//		if (ru_size == RU_SIZE_26_TONES) {
//			Ndbps = 8*180;
//		}
//		else if (ru_size == RU_SIZE_52_TONES) {
//			Ndbps = 8*360; //RU-52, MCS6, 1SS (corresponds to a data rate of 15.9Mbps)
//		}
//		else if (ru_size == RU_SIZE_106_TONES) {
//			Ndbps = 8*765;
//		}
//		else if (ru_size == RU_SIZE_242_TONES) {
//			Ndbps = 8*1755;
//		}
//		else if (ru_size == RU_SIZE_484_TONES) {
//			Ndbps = 8*3510;
//		}
//	}

	ppdu_duration = 40 + ceil((16 + psduLen + 6.0)/Ndbps) * (12.8 + 0.8);
	return ppdu_duration;
}

int getOfdmaAMpduDuration(int mcs, int ru_size, int ampdu_len_vi, int mpdulen_vi, int ampdu_len_ha, int mpdulen_ha, int bw) {
	int psduLen = (44 + mpdulen_vi) * 8 * ampdu_len_vi + (44 + mpdulen_ha) * 8 * ampdu_len_ha;
	return getPpduDuration(mcs, ru_size, psduLen, bw);
}

int getEdcaAMpduDuration(int mcs, int bw, int ampdu_len, int mpdulen) {
	int ru_size = bw2ru_size(bw);
	// changing this to properly convert mpdulen in bytes into bits
	int psduLen = (44 + mpdulen) * 8 * ampdu_len; // (44 * 8 + mpdulen) * ampdu_len;
	return getPpduDuration(mcs, ru_size, psduLen, bw);
}

struct device_AP {
	//variables for RA STAs for channel contention
	int bt_ha; //backoff sim_time HA
	int cw_ha; //contention window HA
//	int bt_vi; //backoff sim_time VI
//	int cw_vi; //contention window VI

	//variables for RA STAs for RA RU contention
	int obo; //OFDMA BackOff
	int ocw; //OFDMA contention window
	int usedRARU; //to determine if this station used a RA RU that experiences a collision

	//variables used for both channel and RA RU contentions
	long long int lastSent; //the dequeue sim_time of an A-MPDU
	int nSuccAccess_HA; //this is not the number of MDPUs but the number of successfully transmitted A-MPDUs (over both the channel and the RUs)
	long long int delay;
	long long int queueheadTime; // this is the timestamp in us of the packet at queue head; different from dequeueTime when node cannot flush the buffer
								 // fully in which case queueheadTime<dequeueTime.
	// variables for EDCA params
	int edca_ampdu_len;
	int edca_ampdu_duration;

	// variables for OFDMA params
	int ofdma_ampdu_len;
	int ofdma_ampdu_duration;
	int sampleCount; // # of samples in buffer
	int nTx; // number of EDCA MPDUs transmitted
	bool incVidCount;
	unsigned int max_duration, num_dl_STAs, current_duration;
	vector<bool> dl_stas;
	vector<long long int> last_packet_ha, current_size;
	vector<int> dl_stas_ru, ampduLength_kin;
	vector<int> interAccess, interAccess_ha, interAccess_ha_vid , apmdu_length, sampleAccessDelay, accessdelay;
	long long int accessTimeEnd_ha, lastAccess=0;
	int max_bt_ha, index_ap, generated_ha=0, dropped_ha=0, count_remove_drop=0, count_remove_sent=0, queuesize, haptic_dur_dl_delay;

	struct delays{
		vector<int> HA;
		vector<int> VI;
	};
	delays delaysList;

	float time_collision, time_send, time_idle, time_staSend, time_dataSend, time_staDataSend;

};



struct device_sta {
	//variables for RA STAs for channel contention
	int bt_ha; //backoff sim_time HA
	int cw_ha; //contention window HA
	int bt_vi=10; //backoff sim_time VI
	int cw_vi; //contention window VI


	//variables used for both channel and RA RU contentions
	long long int lastSent_ha, lastSent_vi; //the dequeue sim_time of an A-MPDU
	int nSuccAccess_HA, nSuccAccess_VI, nSuccAccess_mu_HA, nSuccAccess_mu_VI, nSuccAccess_su_HA, nSuccAccess_su_VI; //this is not the number of MDPUs but the number of successfully transmitted A-MPDUs (over both the channel and the RUs)
	long long int delay;
	long long int queueheadTime; // this is the timestamp in us of the packet at queue head; different from dequeueTime when node cannot flush the buffer
								 // fully in which case queueheadTime<dequeueTime.
	// variables for EDCA params
	int edca_ampdu_len;
	int edca_ampdu_duration;

	// variables for OFDMA params
	int ofdma_ampdu_len;
	int ofdma_ampdu_duration;
	int sampleCount; // # of samples in buffer
	int nTx; // number of EDCA MPDUs transmitted
	bool incVidCount, ulofdma_just_sta, vid_last;
	struct delays{
		vector<int> HA;
		vector<int> VI;
	};
	delays delaysList, delays_su, delays_mu;
	vector<int> accessTimeVec_ha, accessTimeVec_vi, sampleAccessDelay, sampleAccessDelayVid, accessdelay, interAccess_ha, ampduLength_ha;
	long long int lastAccess_ha, lastAccess_vi, accessTimeEnd_ha, lastAccess_pois_ha;
	int max_bt_ha, max_bt_vi, count=0, generated_ha=0, generated_vi=0, dropped_ha=0, dropped_vi=0, count_remove_drop=0, count_remove_sent=0, fragments_sent=0, frames_sent=0,
			hap_frames_sent=0, vid_frames_sent=0, sta_collision_duration, haptic_dur_ul, ul_duration, haptic_dur_ul_delay;
	float time_collision, time_send;
	string send_media_mu="I";
};

struct stats_struct {
	int nCollisions; //collisions on the different RA RUs
	int nNoCollisions; //successful transmissions on RA RUs
	int nRATx; //records the number of transmitted MPDUs on RA RUs. The total transmitted MPDUs = nRATx + nSATx
	int nSATx; //records the number of transmitted MPDUs on SA RUs. The total transmitted MPDUs = nRATx + nSATx
};

struct dropped{
	int ha;
	int vi;
};

stats_struct ofdma_stats;
//ofdma_stats.nCollisions = 0;
//ofdma_stats.nNoCollisions = 0;
//ofdma_stats.nRATx = 0;
//ofdma_stats.nSATx = 0;

device_AP APSta;
device_sta *RAStas = NULL; //it is possible that nRAstas=0
dropped AC_packets, local_packets;


vector<int> delay_isolated;
string media, apMedia;
//int maxRUs = getMaxRUsPerChannelWidth(bw, ru_size);
int nSARUs, nDLSTAs, nULSTAs; //this is the number of SA RUs and also the number of SA STAs

int queue_size, max_duration=0, max_duration_STA, * access_ap, ap_collision_duration=80;
vector<vector<int>> delays;


vector<bool> dl_stas;
vector<int> ampdu_DL_currentsize, ampdu_DL_currentduration, ul_zero_ofdma_delay, ul_zero_edca_delay, dl_zero_ofdma_delay,
			sta_interAccess_mu_ha_vid, sta_interAccess_mu_ha, sta_interAccess_su_ha_vid, sta_interAccess_su_ha, sta_interAccess_ha;

long long int sta_maxbt=0,ap_maxbt=0, *lastSent_temp, totalLost_stah = 0, totalLost_stav, totalLost_ap, numCollisions, numVidCollisions;
std::multimap<int,int> ul_sampleCount, ul_ha_sampleCount, dl_sampleCount;
int timeleft, dl_ofdma_batch, ul_ofdma_batch, *accesstemp, *accesstemp_su, *accesstemp_mu, highest_sta;
std::map<char,int>::reverse_iterator rit;
vector<int> stas_dl, stas_ul, ul_ofdma_dur, ul_ofdma_data, ul_ofdma_overhead;
bool dlofdma_interrupted, ulofdma_just_ap=false, inside_ulofdma=false;
vector<int> *delays_mu, *delays_su, *delaystemp, AP_accessTime, APSta_kinFramesSent, dlofdma_duration, ulofdma_duration;

vector<vector<unsigned int>> pacQ_STA_ha, pacQ_AP_ha, retry_cnt_STA_ha, retxQ_STA_ha, retry_cnt_AP_ha, retxQ_AP_ha, AP_interAccess;
vector<vector<unsigned int>> pacQ_STA_vi, pacQ_STA_vi_size, retry_cnt_STA_vi, retxQ_STA_vi;
vector<vector<unsigned int>> * pacQ_holder, *retxQ_holder, *retry_cnt_holder, *pacQ_size_holder;
vector<float> AP_queuesize, STA_HA_queuesize, STA_VI_queuesize, ulofdmadelay_sta, ulofdmadelay_ap,
				nonulofdmadelay_sta, nonulofdmadelay_ap, otherdelay;

int nCollisions = 0, nNoCollisions = 0, packet_size, duration, retryCount, ulofdma_start_time, dlofdma_start_time;
int nTx = 0; //this is the number of transmitted MPDUs using EDCA (UL OFDMA transmissions are excluded and are recorded using other variables)
std::ofstream staO_file("./log/staO_file.txt"), ap_packet_file("./log/ap_packet_file.txt"), ofdma_track_file("./log/ofdma_track_file.txt");
string device;


dropped updateRetryInfo(int n, int len, int retryCount_local, bool StaDevice, long long int time_now){

	int count_remove_drop=0;
	local_packets.ha = 0;
	local_packets.vi = 0;
	device = StaDevice ? "STA ": "AP ";
//	if (StaDevice){
//		cout << "sim_time: " << time_now <<  " media: " << media << " BT_ha: " << RAStas[n].bt_ha << " BT_vi: " << RAStas[n].bt_vi << endl;
//	}
//	else{
//		cout << "sim_time: " << time_now << " media: " << media << " BT_ha: " << APSta.bt_ha << endl;
//	}
	// if empty, push new entries
	if ((n==0) && StaDevice && (media.compare("VI")==0)){
		video_file << "sim_time -- " << time_now << endl;
	}
	if ((*retry_cnt_holder)[n].empty()){
		(*retry_cnt_holder)[n].push_back(1);
		(*retxQ_holder)[n].push_back((*pacQ_holder)[n][len]);

		// ---------------------------------------------------- (n==0) && StaDevice
//		if ((media.compare("VI")==0)){
//			staO_file << "\n" << device << " " << n << "    sim_time: " <<  time_now << "    Adding initial " << media << endl;
//			staO_file << "******************" << endl;
//			cout << "\n" << device << " " << n << "    sim_time: " <<  time_now << "    Adding initial " << media << endl;
//			cout << "******************" << endl;
		sta_file << "\n adding new entry when empty " << media << " queue. Q-size: " << (*pacQ_holder)[n].size() << endl;
		if ((n==0) && StaDevice && (media.compare("VI")==0)){
			video_file << "\n adding new entry when empty." << endl;
		}
		for (int x=0; x<(*retry_cnt_holder)[n].size(); x++){
			staO_file << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;
			//				cout << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;
			if ((n==0) && StaDevice){
				sta_file << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;
				if (media.compare("VI")==0){
					video_file << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;
				}
			}
		}
		if ((n==0) && StaDevice && (media.compare("VI")==0)){
			video_file << "\n -------------------- " << time_now << endl;
		}
//			staO_file << "******************" << endl;
//			cout << "******************" << endl;
//			cout << "Last entry in Q: " << (*pacQ_holder)[n].back() << "\n" << endl;

//		}
		// ----------------------------------------------------

	}

	else {
		// update existing entries
		if (((*pacQ_holder)[n][len]>=(*retxQ_holder)[n].back())){
			sta_file << "\n updating entry for " << media << " queue. Q-Size: " << (*pacQ_holder)[n].size() << endl;

			if ((n==0) && StaDevice && (media.compare("VI")==0)){
				video_file << "\n updating entry for " << media << " queue. Q-Size: " << (*pacQ_holder)[n].size() << endl;
			}
			for (int k=0;k<(*retxQ_holder)[n].size();k++){
				(*retry_cnt_holder)[n][k] += 1;
				if ((n==0)&&StaDevice){
					sta_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
					if (media.compare("VI")==0){
						video_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
					}

				}
			}


			// ---------------------------------------------------- StaDevice
//			if ((media.compare("VI")==0)){
//				staO_file << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Updating " << media << endl;
//				staO_file << "******************" << endl;
//				cout << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Updating " << media << endl;
//				cout << "******************" << endl;
//				for (int x=0; x<(*retxQ_holder)[n].size(); x++){
//					staO_file << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;
//					cout << (*retxQ_holder)[n][x] << "   " << (*retry_cnt_holder)[n][x] << endl;

//				}
//				staO_file << "******************" << endl;
//				cout << "******************" << endl;
//				cout << "Last entry in Q: " << (*pacQ_holder)[n].back() << endl;


//			}

			// ----------------------------------------------------

		}
		// add new entries
		if (((*pacQ_holder)[n][len]>(*retxQ_holder)[n].back())){
			sta_file << "\n adding new entry for " << media << " queue. Q-size: " << (*pacQ_holder)[n].size() << endl;

			if ((n==0) && StaDevice && (media.compare("VI")==0)){
				video_file << "\n adding new entry for " << media << " queue. Q-size: " << (*pacQ_holder)[n].size() << endl;
			}


			(*retxQ_holder)[n].push_back((*pacQ_holder)[n][len]);
			(*retry_cnt_holder)[n].push_back(1);
			for (int k=0;k<(*retxQ_holder)[n].size();k++){
				if ((n==0)&&StaDevice){
					sta_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
					if (media.compare("VI")==0){
						video_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
					}

				}
			}

			// ---------------------------------------------------- (n==0) &&
//			if ((media.compare("VI")==0)){
//				staO_file << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Adding " << media << endl;
//				staO_file << "******************" << endl;
//				cout << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Adding " << media << endl;
//				cout << "******************" << endl;
//				for (int x=0; x<(*retxQ_holder)[n].size(); x++){
//					staO_file << (*retxQ_holder)[n][x] << "    " <<  (*retry_cnt_holder)[n][x] << endl;
//					cout << (*retxQ_holder)[n][x] << "    " <<  (*retry_cnt_holder)[n][x] << endl;
//
//				}
//				staO_file << "******************" << endl;
//				cout << "******************" << endl;
//				cout << "Last entry in Q: " << (*pacQ_holder)[n].back() << endl;


//			}
			// ----------------------------------------------------
		}


		// delete MPDUs if retry count threshold is exceeded
		if ((*retry_cnt_holder)[n].front()>retryCount_local){
			for(int y=0;y<(*pacQ_holder)[n].size();y++){

				if ((*retxQ_holder)[n].front()>=(*pacQ_holder)[n][y]){
					++count_remove_drop;
//					printf("\n sim_time: %d  Dropping %d packets of AC-%s from %s\n", time_now, count_remove_drop, media.c_str(), device.c_str());
				}
				else{
					break;
				}
			}


			(*pacQ_holder)[n].erase((*pacQ_holder)[n].begin(), (*pacQ_holder)[n].begin()+count_remove_drop);
			(*retry_cnt_holder)[n].erase((*retry_cnt_holder)[n].begin(), (*retry_cnt_holder)[n].begin()+1);
			(*retxQ_holder)[n].erase((*retxQ_holder)[n].begin(), (*retxQ_holder)[n].begin()+1);
			if ((media.compare("HA")==0)){
				local_packets.ha =count_remove_drop;

//				if (!StaDevice){
//					cout << "AP " << n << " Q-size" << (*pacQ_holder)[n].size() << endl;
//
//				}
			}
			else if ((media.compare("VI")==0)){
				local_packets.vi =count_remove_drop;
			}

			sta_file << "\n deleting entry from " << media << " queue. Q-size: " << (*pacQ_holder)[n].size() << endl;
			if ((n==0) && StaDevice && (media.compare("VI")==0)){
				video_file << "\n deleting entry from " << media << " queue. Q-size: " << (*pacQ_holder)[n].size() << endl;
			}

			for (int k=0;k<(*retxQ_holder)[n].size();k++){
				sta_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
				if ((n==0) && StaDevice && media.compare("VI")==0){
					video_file << (*retxQ_holder)[n][k] << "   " << (*retry_cnt_holder)[n][k] << endl;
				}

			}
			// ---------------------------------------------------- (n==0) &&
//			if ((media.compare("VI")==0)){
//				staO_file << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Discarded " << count_remove_drop << " entries from RTRQ" << endl;
//				staO_file << "******************" << endl;
//				cout << "\n" << device << " " << n << "    sim_time: " <<  time_now << "   Discarded " << count_remove_drop << " entries from RTRQ" << endl;
//				cout << "******************" << endl;
//				for (int x=0; x<(*retxQ_holder)[n].size(); x++){
//					staO_file << (*retxQ_holder)[n][x] << "    " << (*retry_cnt_holder)[n][x] << endl;
//					cout << (*retxQ_holder)[n][x] << "    " << (*retry_cnt_holder)[n][x] << endl;

//				}
//				staO_file << "******************" << endl;
//				cout << "******************" << endl;
//				cout << "First entry in Q: " << (*pacQ_holder)[n].front() << "    Last entry in Q: " << (*pacQ_holder)[n].back() << endl;


//			}

			// ----------------------------------------------------
		}
	}

	return local_packets;
}

struct wlan_result simulate_wlan(const int bw, int nRAStas, int mcs, bool newSta, int max_ofdma_duration, bool ofdma_bw_mode, int buffer_limit, float fragment_threshold) {
	lostPackFile.open ("./log/lostPackets.txt", std::ofstream::out | std::ofstream::app);
	time_track.open ("log/time_track.txt", std::ofstream::out | std::ofstream::app);
	ofdma_track.open ("log/ofdma_track.txt", std::ofstream::out | std::ofstream::app);
	vid_metadata_file.open ("log/vid_metadata_file.txt", std::ofstream::out | std::ofstream::app);
	throughput_file.open ("log/throughput_track.txt", std::ofstream::out | std::ofstream::app);

	sta_file.open ("log/sta_file.txt");
	video_file.open ("log/video_file.txt");

   //first, check params and print a summary
	cout << "\n\nSwitch ---------- " << nRAStas << "\t" << newSta << endl;

	fragments_per_frame=floor(fragment_threshold*PACKET_SIZE_BWD_VI*1.0/FRAGMENT_SIZE);
//	if ((nRAStas!=14) && newSta){
//		for (int i=0; i<nRAStas-1; i++){
//			cout << "\n Will start loading" << endl;
//			totalLost_stah += RAStas[i].dropped_ha;
//			totalLost_stav += RAStas[i].dropped_vi;
//			totalLost_ap += APSta.dropped_ha;
//			cout << totalLost_stah << "\t" ;
//		}
//		cout << "\n\n Will load now" << endl;
//		lostPackFile << nRAStas-1 << "\t" << totalLost_stah << "\t" << totalLost_stav << "\t" << totalLost_ap << endl;
//		totalLost_stah = 0;
//		totalLost_stav = 0;
//		totalLost_ap = 0;
//	}

	int duration_tf = 44, duration_multi_sta_back = 44, duration_back = 44, numaccess=0, bsrptime = 44, bsrtime = 44, no_fragments=PACKET_SIZE_BWD_VI/FRAGMENT_SIZE,
			tempframes=0, ha_ulofdma_episode=0, ap_access_counter=0, vi_ulofdma_episode=0, vi_empty_counter=0, time_overhead=0, highest_sta_hap_size, vid_frames,
			vi_fragments, ha_frames, total_length_dl, total_length_ul, vi_stas, ha_only_stas, total_vid_fragments=0, total_hap_frames=0, total_kin_frames=0,
			rts_cts_count_noCollision=0, overhead_collision=0, edca_access=0, ul_ofdma_access=0, dl_ofdma_access=0, hap_frame_length, vid_fragment_length,
			txed_vi_fragments, txed_ha_frames;

	long long int ul_zero_ofdma_ampdu=0, ul_zero_ofdma_access=0, ul_zero_edca_access=0, ul_zero_edca_ampdu=0,
			dl_zero_ofdma_ampdu=0, dl_zero_ofdma_access=0, ampdu_sta_su_VI=0, ampdu_sta_su_HA=0, *ampdu_len, ampdu_sta_mu_VI=0,
			ampdu_sta_mu_HA=0, ampdu_ap_HA=0, ampdu_ap_VI=0, total_hapFrames=0, total_vidFrames=0, total_kinFrames=0;
	int last_packet_ha, last_packet_vi, buffer_size_ap=0, buffer_size_sta=0, buffer_size_sta_count=0, buffer_size_ap_count=0;
	long long int UL_Tx_count = 0, AP_Tx_count=0; // # UL packet tx., # DL packet tx.
	long long int dl_ofdma_tot_dur=0, ul_ofdma_tot_dur=0, dl_ofdma_tot_frame=0, ul_ofdma_tot_frame=0, throughput;
	int nSAStas, ul_ofdma_count=0, nStas_dl, nStas_ul, extra;
	int nSenders_ha = 0, nSenders_vi = 0, slotTimeCount=0, ha_index=100, vi_index=100, vi_ofdma_count=0, vi_edca_count=0;
	bool ap_wins, vid_exhausted, dl_firsttime, ul_firsttime;

	int temp_sta_index;

	global_file.open ("ResultsFiles/Latency/Global/global.txt", std::ofstream::out | std::ofstream::app);
	global_buffer.open ("ResultsFiles/Latency/Global/global_buffer.txt", std::ofstream::out | std::ofstream::app);
	frag_thresh_file.open ("ResultsFiles/Latency/Global/frag_thresh.txt", std::ofstream::out | std::ofstream::app);
	temp_file.open ("log/temp_file.txt", std::ofstream::out | std::ofstream::app);
	hap_delay_p_file.open ("log/hap_delay_p.txt", std::ofstream::out | std::ofstream::app);
	vid_delay_p_file.open ("log/vid_delay_p.txt", std::ofstream::out | std::ofstream::app);
	kin_delay_p_file.open ("log/kin_delay_p.txt", std::ofstream::out | std::ofstream::app);



	//-------------------------- START OF PACKAGE 1 --------------------------//
	if (nRAStas < 0) nRAStas = 0;
	if (mcs < 0) mcs = 0;
	if (mcs > 11) mcs = 11;
//	if (nRARUs < 0) nRARUs = 0;
//	//if (nRARUs > maxRUs) nRARUs = maxRUs;


//	nSARUs = maxRUs - nRARUs;

	pacQ_STA_ha.clear();
	pacQ_STA_vi.clear();
	pacQ_STA_vi_size.clear();
	pacQ_AP_ha.clear();
	retry_cnt_STA_ha.clear();
	retxQ_STA_ha.clear();
	retry_cnt_AP_ha.clear();
	retxQ_AP_ha.clear();
	retry_cnt_STA_vi.clear();
	retxQ_STA_vi.clear();
	AP_queuesize.clear();
	STA_HA_queuesize.clear();
	STA_VI_queuesize.clear();


#if 0
    printf("Channel Width                     : %d MHz\n", bw);
    printf("RU size                           : %d tones\n", ru_size);
    printf("Max number of RUs                 : %d\n", maxRUs);
    printf("Number of SA RUs (and SA STAs)    : %d\n", nSARUs);
    printf("Number of RA RUs                  : %d\n", nRARUs);
    printf("Number of STAs (Random Access)    : %d\n", nRAStas);
    printf("MCS index                         : %d\n", mcs);
#endif

//    if (maxRUs <= 0) {
//    	printf("maximum number of RUs (maxRUs=%d) should be > 0\n", maxRUs);
//    	exit(0);
//    }
//
//    if (m_nApAntennas > 1 && ru_size < RU_SIZE_106_TONES) {
//    	printf("both DL and UL MU-MIMO are possible on RU size >= 106 tones\n");
//    	exit(0);
//    }



	/* initialize random seed: */
    srand (time(NULL));
    //put it here because there is a variable called "sim_time", to avoid the error : 'sim_time' cannot be used as a function

    int sim_time = 0; //sim_time in µs
    int temp_counter_ap=0,temp_counter_stas=0, packet_size_vi, num_frames_sent;
	for(int i=0;i<nRAStas;i++){
		APSta.last_packet_ha.push_back(0);
	}
	APSta.last_packet_ha.resize(nRAStas);

	std::ofstream output_file_AP("./log/APdelays.txt"), delay_file_STA_VI("./log/STAdelaysCollect_VI.txt"),
			delay_file_STA_HA("./log/STAdelaysCollect_HA.txt"), delay_file_AP_HA("./log/APdelaysCollect_HA.txt");
	std::ofstream output_file_STA("./log/STA-AMPDU.txt"), output_file_isolated("./log/delay-DL-isolated.txt");
	std::ofstream vid_delay_file("./log/vid_delay.txt"), batch_dur_file("./log/batch_duration.txt");
	std::ofstream txtime_file_sta("./log/txtime_sta.txt"), txtime_file_ap("./log/txtime_ap.txt"),
				delayFile("./log/delayFile.txt"), logging_file("./log/logging.csv");

	bool apCollision = false;


	if (nRAStas > 0) {
	    RAStas = new device_sta[nRAStas];
	}


	vector<int> txtime_ap, txtime_sta;
	int initial;


//	for (int i=0;i<nRAStas;i++){
//		cout << "here" << endl;
//		pacQ_STA_ha.push_back(vector<unsigned int>());
//		initial = rand() % HA_DURATION;
//		if(initial<=sim_time){
//			pacQ_STA_ha[i].push_back(initial);
//		}
//		pacQ_AP_ha.push_back(vector<unsigned int>());
//
//		initial = rand() % HA_DURATION;
//		if(initial<=sim_time){
//			pacQ_AP_ha[i].push_back(initial);
//		}
//		retry_cnt_STA_ha.push_back(vector<unsigned int>());
//		retxQ_STA_ha.push_back(vector<unsigned int>());
//		retry_cnt_AP_ha.push_back(vector<unsigned int>());
//		retxQ_AP_ha.push_back(vector<unsigned int>());
//
//		pacQ_STA_vi.push_back(vector<unsigned int>());
//		initial = rand() % VI_DURATION;
//		if(initial<=sim_time){
//			pacQ_STA_vi[i].push_back(initial);
//		}
//		retry_cnt_STA_vi.push_back(vector<unsigned int>());
//		retxQ_STA_vi.push_back(vector<unsigned int>());
//	}
	int temp_sample_time = - HA_DURATION;
	temp_file << "\n\n ----------- STARTING " << nRAStas << " STAS -----------\n\n" << endl;
	for (int i=0;i<nRAStas;i++){
		pacQ_STA_ha.push_back(vector<unsigned int>());
		RAStas[i].lastSent_ha=rand() % HA_DURATION - HA_DURATION;
		vid_delay_file << "First H sample: " << RAStas[i].lastSent_ha << endl;
//		pacQ_STA_ha[i].push_back(0);
		pacQ_AP_ha.push_back(vector<unsigned int>());
		APSta.last_packet_ha[i]=temp_sample_time;
		vid_delay_file << "First K sample: " << APSta.last_packet_ha[i] << endl;
//		pacQ_AP_ha[i].push_back(0);
		retry_cnt_STA_ha.push_back(vector<unsigned int>());
		retxQ_STA_ha.push_back(vector<unsigned int>());
		retry_cnt_AP_ha.push_back(vector<unsigned int>());
		retxQ_AP_ha.push_back(vector<unsigned int>());
		pacQ_STA_vi.push_back(vector<unsigned int>());
		pacQ_STA_vi_size.push_back(vector<unsigned int>());
		AP_interAccess.push_back(vector<unsigned int>());

//		vid_delay_file << "STA 0: before generating frame: " << pacQ_STA_vi[i].size() << endl;
		for (int x=0;x<int(PACKET_SIZE_BWD_VI*1.0/FRAGMENT_SIZE); x++){
//			pacQ_STA_vi[i].push_back(0);
			RAStas[i].lastSent_vi=RAStas[0].lastSent_ha+HA_DURATION-VI_DURATION;

		}
		vid_delay_file << "First V sample: " << RAStas[i].lastSent_vi << endl;
		temp_file << "FrameTime: " << 0 << "\tSTA: " << i << "\t#Fragments: " << int(PACKET_SIZE_BWD_VI*1.0/FRAGMENT_SIZE) << endl;

//		pacQ_STA_vi_size[i].push_back(int(PACKET_SIZE_BWD_VI*1.0/FRAGMENT_SIZE));
//		vid_delay_file << "STA 0:   #FragmentsGenerated: " << pacQ_STA_vi[i].size() << endl;
		retry_cnt_STA_vi.push_back(vector<unsigned int>());
		retxQ_STA_vi.push_back(vector<unsigned int>());
		AP_accessTime.push_back(0);
		APSta_kinFramesSent.push_back(0);
	}

	//set BT and OBO for all RAStas; only initialization irrespective of channel access method (pure EDCA, pure OFDMA, default OFDMA)
	// bt and cw are for EDCA; obo and ocw for OFDMA
	for (int i = 0; i < nRAStas; i++) {
		RAStas[i].cw_ha = 0;
//		RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1);

		//			RAStas[i].bt_vi = rand() % (CW_MIN_VI + 1);
		//			RAStas[i].cw_vi = CW_MIN_VI;

		// dequeuetime is used to measure the channel delays
		//RAStas[i].dequeueTime = 0; //under high load condition, the first A-MPDU is dequeued at t=0
		RAStas[i].nSuccAccess_HA = 0;
		RAStas[i].nSuccAccess_VI = 0;
		RAStas[i].nSuccAccess_mu_HA = 0;
		RAStas[i].nSuccAccess_mu_VI = 0;
		RAStas[i].nSuccAccess_su_HA = 0;
		RAStas[i].nSuccAccess_su_VI = 0;
		RAStas[i].queueheadTime = 0;
		RAStas[i].delaysList.HA.clear();
		RAStas[i].delaysList.VI.clear();
		RAStas[i].delays_mu.HA.clear();
		RAStas[i].delays_mu.VI.clear();
		RAStas[i].delays_su.HA.clear();
		RAStas[i].delays_su.VI.clear();
		RAStas[i].lastAccess_ha=0;
		RAStas[i].incVidCount=false;
	}

	APSta.cw_ha = 0;
//	APSta.bt_ha = rand() % (APSta.cw_ha + 1);
	APSta.queueheadTime=0;
	APSta.sampleCount=0;
	APSta.nTx=0;
	APSta.nSuccAccess_HA=0;
	APSta.generated_ha=0;
	APSta.delaysList.HA.clear();
	APSta.incVidCount=false;
	APSta.accessTimeEnd_ha = 0;

	delay_isolated.clear();
	stas_dl.clear();
	txtime_ap.clear();
	txtime_sta.clear();

	long long int sum_dur=0, packet_range=0, ha_ulofdma=0;
	bool ap_tosend, APhasData, vi_empty=true, ha_empty=true, vid_last=false;
	//bool intra_OFDMA=false;


	//-------------------------- END OF PACKAGE 1 --------------------------//

	//-------------------------- START OF PACKAGE 2 --------------------------//
    // Generating new HV packets & setting the CW of AP/STAs
	cout << "\n ----------- loop restarting ----------- \n\n\n" << endl;
	sta_file << "No. of STAs: " << nRAStas << endl;
	sim_time=0;
	while (sim_time < MAX_SIMULATION_TIME_US) {
		ha_index=100;
		vi_index=100;
//		if (sim_time<0)
//			exit(0);
		//printf(" -------------- sim_time: %d --------------\n", sim_time);

		ap_tosend=false;
		APSta.incVidCount=false;
		APhasData = false;

		// STA packet generation
		for (int i=0; i<nRAStas; i++){

			// haptic packet generation
			if (pacQ_STA_ha[i].empty()){
				last_packet_ha = RAStas[i].lastSent_ha;
//				vid_delay_file << "HA last packet: " << last_packet_ha << endl;
			}
			else{
				last_packet_ha = pacQ_STA_ha[i].back();
			}

//			vid_delay_file << "SimTime-lastpacket = " << last_packet_ha-sim_time << "\t" << sim_time << "\t" << last_packet_ha << endl;

			if (sim_time-last_packet_ha>=HA_DURATION){
				for (int j=1; j<=floor((sim_time-last_packet_ha)*1.0/HA_DURATION); j++){
					pacQ_STA_ha[i].push_back(last_packet_ha+HA_DURATION*j);
					++RAStas[i].generated_ha;
//					vid_delay_file << "Generated " << RAStas[i].generated_ha << " samples" << endl;
//					exit(-1);
				}

			}

//			vid_delay_file << "Q size: " << pacQ_STA_ha[i].size() << endl;
			if (pacQ_STA_ha[i].size()>buffer_limit){
				vid_delay_file << "Time: " << sim_time << "  STA-" << i<<  "\tQueue spill-over dropping " << pacQ_STA_ha[i].size()-buffer_limit << endl;
				RAStas[i].dropped_ha += (pacQ_STA_ha[i].size()-buffer_limit);
				pacQ_STA_ha[i].erase(pacQ_STA_ha[i].begin(), pacQ_STA_ha[i].begin()+
						pacQ_STA_ha[i].size()-buffer_limit);


			}

			// video packet generation
			if (pacQ_STA_vi[i].empty()){
				last_packet_vi = RAStas[i].lastSent_vi;
			}
			else{
				last_packet_vi = pacQ_STA_vi[i].back();
			}

//			vid_delay_file << "sim_time: " << sim_time << "\tLastPacket: " << last_packet_vi << endl;
			if ((sim_time-last_packet_vi)>=VI_DURATION){ // assuming the video sampling rate is 60Hz

				// frame generation
				for (int j=1; j<=floor((sim_time-last_packet_vi)*1.0/VI_DURATION); j++){
					packet_size_vi = (PACKET_SIZE_BWD_VI);// + ((rand() % 9)-4)*FRAGMENT_SIZE; // packet size \in [15000, 25000]
					pacQ_STA_vi_size[i].push_back(int(packet_size_vi*1.0/FRAGMENT_SIZE));
//					temp_file << "STA: " << i << "\ttime: " << sim_time << "\tPacketSize: " << packet_size_vi << endl;
					// fragment generation
					for (int x=0;x<int(packet_size_vi*1.0/FRAGMENT_SIZE); x++){
							pacQ_STA_vi[i].push_back(last_packet_vi+VI_DURATION*j);
					}
					temp_file << "FrameTime: " << last_packet_vi+VI_DURATION*j << "\tSTA: " << i << "\t#Fragments: " << int(packet_size_vi*1.0/FRAGMENT_SIZE) << endl;
					++RAStas[i].generated_vi;
					vid_delay_file << "Time: " << sim_time << "\tVid frames generated: " << RAStas[i].generated_vi << endl;
				}
			}


			// Measuring avg. buffer size only for STA 1
			if (i==1){
				buffer_size_sta += pacQ_STA_ha[i].size();
				++buffer_size_sta_count;
			}
		}

		// AP packet generation
		for (int i=0; i<nRAStas; i++){
			// haptic packet generation
			if (pacQ_AP_ha[i].empty()){
				last_packet_ha = APSta.last_packet_ha[i];
			}
			else{
				last_packet_ha = pacQ_AP_ha[i].back();
			}

			if ((sim_time-last_packet_ha)>=HA_DURATION){

				for (int j=1; j<=floor((sim_time-last_packet_ha)*1.0/HA_DURATION); j++){
					pacQ_AP_ha[i].push_back(last_packet_ha+HA_DURATION*j);
					++APSta.generated_ha;
				}
				vid_delay_file << "AP packet generated" << endl;
			}

			if (pacQ_AP_ha[i].size()>buffer_limit){
				vid_delay_file << "AP-" << i <<  "\tQueue spill-over dropping " << pacQ_AP_ha[i].size()-buffer_limit << endl;
				APSta.dropped_ha += (pacQ_AP_ha[i].size()-buffer_limit);
				pacQ_AP_ha[i].erase(pacQ_AP_ha[i].begin(), pacQ_AP_ha[i].begin()+
						pacQ_AP_ha[i].size()-buffer_limit);


			}
		}

		nSenders_ha = 0;
		nSenders_vi = 0; // resetting CW of AC_VI even though there is a intra-STA collision


		// setting CW and BT for a new sample at the STAs
		sta_file << "-----------------------" << endl;
		for (int i=0; i<nRAStas; i++){
			RAStas[i].incVidCount = false;
			// update STA  bt, cw when (i) a sample is pending in buffer and STA had just made a Tx.
			//						   (ii) packet(s) were dropped due to RLC threshold
			// when above conditions don't hold, then either the STA has nothing to Tx. or it is in the middle of contention
//			if(pacQ_STA_ha[i].empty()){
//				RAStas[i].bt_ha=-1;
//				RAStas[i].cw_ha = CW_MIN_HA;
//			}

//			ensure this occurs only for first time -- set it to zero???
//			inside 'if' condition -- && retry_queue is empty?
			if (((pacQ_STA_ha[i].size()>0) && (RAStas[i].bt_ha < 0))){
				vid_delay_file << "STA-" << i << "\tTime: " << sim_time << "\tQ-head: " << pacQ_STA_ha[i].front() << endl;
//				if (sim_time-pacQ_STA_ha[i].front()>0.1*HA_DURATION){ //

					vid_delay_file << "Already backed off" << endl;
					RAStas[i].cw_ha = CW_MIN_HA;
					RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1); // 100000000  for ver-2
					logging_file << sim_time << ";" << sim_time+RAStas[i].bt_ha*SLOT_TIME << ";STA" << i<< ";B;-" << endl;

//				}
//				else{
//					vid_delay_file << "Not yet backed off" << endl;
//					RAStas[i].cw_ha = 0;
//					RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1); // 100000000  for ver-2
//				}

				sta_file << "New HA frame" << endl;
				//RAStas[i].accessTime=sim_time;
			}
			else if((pacQ_STA_ha[i].empty())){
				RAStas[i].bt_ha=-1;
				RAStas[i].cw_ha = 0;
			}

//			if (inside_ulofdma){
////				vid_delay_file << "STA-" << i << "\tBT: " << RAStas[i].bt_ha << "\tCW: " << RAStas[i].cw_ha << endl;
//			}



			if (((pacQ_STA_vi[i].size()>0) && (RAStas[i].bt_vi < 0))){
				//RAStas[i].cw_vi = CW_MIN_VI;
				//RAStas[i].bt_vi = rand() % (CW_MIN_VI + 1);

				//sta_file << "New VI frame" << endl;


//				printf("4 -- STA %d  last sent: %d   VI queue size %d   backing off to %d\n", i, RAStas[i].lastSent_vi,
//						pacQ_STA_vi[i].size(), RAStas[i].bt_vi);
				// ----------------------------------------------------------
//				if (i==0){
//					staO_file << sim_time << ":  backing off to " << RAStas[i].bt_vi << endl;
//					cout << sim_time << ":  backing off to " << RAStas[i].bt_vi << endl;
//
//				}
				// ------------------------------------------------------------
				//RAStas[i].accessTime=sim_time;
			}

			// STAs (with old or even new packets) done with backoff
			if (RAStas[i].bt_ha == 0 && !pacQ_STA_ha[i].empty()) {
				ha_index = i;
				nSenders_ha += 1;
				RAStas[i].bt_ha = -1; //make it invalid so we can set it later
								   //do not set it here, because BT depends on the transmission status (success of failure)
			}

//			if (RAStas[i].bt_vi == 0) {
//				vi_index = i;
//				nSenders_vi += 1;
//				RAStas[i].bt_vi = -1; //make it invalid so we can set it later
//				//do not set it here, because BT depends on the transmission status (success of failure)
//			}

			sta_file << "STA-" << i << "   H: " << RAStas[i].bt_ha << "   V: " << RAStas[i].bt_vi << "   Q-size HA: " <<
					pacQ_STA_ha[i].size() << "   Q-size VI: " << pacQ_STA_vi[i].size() <<  endl;

		}

		sta_file << "-----------------------" << endl;

		//check if the AP will send
		ap_wins = false;

		// AP has new packets after the last Tx.
		for (int i=0;i<pacQ_AP_ha.size();i++){
//			vid_delay_file << "AP BT: " << APSta.bt_ha << endl;
			if (pacQ_AP_ha[i].size()>0){
				if ((APSta.cw_ha==0)  && (APSta.bt_ha < 0)){
//					if (sim_time-pacQ_AP_ha[i].front()>0.1*HA_DURATION){ //
						vid_delay_file << "AP Already backed off" << endl;
						++num_collisions;
						APSta.cw_ha = CW_MIN_HA;
						APSta.bt_ha = rand() % (APSta.cw_ha + 1);
						logging_file << sim_time << ";" << sim_time+APSta.bt_ha*SLOT_TIME << ";AP;B;-" << endl;

//						logging_file << "Time: " << sim_time << "\tAP:    virtual "
//								"collision. Backing off by: " << APSta.bt_ha*SLOT_TIME << "\n" << endl;

//					}
//					else{
//						vid_delay_file << "AP Not yet backed off" << endl;
//						APSta.bt_ha = rand() % (APSta.cw_ha + 1);
//					}

					//APSta.accessTime=sim_time;
				}
				if (APSta.bt_ha == 0) {
					ap_wins = true;
					nSenders_ha += 1;
					APSta.bt_ha = -1; //make it invalid so we can set it later
					//do not set it here, because BT depends on the transmission status (success or failure)
					ha_index = -1;
				}
//				vid_delay_file << "AP    " << "BT: " << APSta.bt_ha << "   CW: " << APSta.cw_ha << endl;
				break;
			}

		}

		sta_file << "AP-" <<  "   H: " << APSta.bt_ha << " Q-size HA: " << pacQ_AP_ha[0].size() << endl;
		sta_file << "-----------------------" << endl;

		// print BT values here
		for (int i=0; i<nRAStas; i++){
			if (pacQ_STA_ha[i].size()){
//				vid_delay_file << "STA-" << i << "\tBT: " <<RAStas[i].bt_ha << "\tCW: " << RAStas[i].cw_ha << endl;
				//%d -- HA - Qsize: %d \t BT: %d \t VI - Qsize: %d \t BT: %d\n",i, pacQ_STA_ha[i].size(), RAStas[i].bt_ha, pacQ_STA_vi[i].size(), RAStas[i].bt_vi);
				if(i==nRAStas-1){
					vid_delay_file << "\n" << endl;
				}
			}

		}
//		printf("\n");
//
//		for (int i=0; i<nRAStas; i++){

//		}
//		printf(" ----------------------------\n");
//
//		printf("------ nSenders-HA: %d \t nSenders-VI: %d\n", nSenders_ha, nSenders_vi);

		// BT should be decreased only when channel is detected free for SLOT_TIME
		// Check if there are STA senders. If yes, BT should not be decreased. So DO NOT decrement BT here


		// AP/STA has to wait for AIFS (in case of EDCA) to start transmitting
//		if (waitAifs) {
//			if (nSenders_ha>0){
//				vid_delay_file << "AIFS-HA: sim_time from " << sim_time << " to " << sim_time + AIFS_HA << endl;
//				sim_time = sim_time + AIFS_HA;
//			}
//			else if (nSenders_vi>0){
//				sim_time = sim_time + AIFS_VI;
//				sta_file << "AIFS-VI: sim_time from " << sim_time << " to " << sim_time + AIFS_VI << endl;
//			}
//			else{
//				vid_delay_file << "Not adding AIFS_HA" << endl;
//			}
//			waitAifs = false;
//		}


		//-------------------------- END OF PACKAGE 2 --------------------------//

		//-------------------------- START OF PACKAGE 3 --------------------------//

		//printf("STA BT: %d \t AP BT: %d \t # senders: %d  \n", RAStas[0].bt, APSta.bt, nSenders);

		/*** Handling (no) collisions and advancing sim_time*/
		//if no senders, advance sim_time with slottime. otherwise, advance sim_time with the transmission duration
		if (nSenders_ha+nSenders_vi == 0) {
			++ slotTimeCount;
//			vid_delay_file << "\nNo collision: Slot sim_time: sim_time from " << sim_time << " to " ;
			sim_time = sim_time + SLOT_TIME; //do not "continue", we should decrease BT
//			vid_delay_file << sim_time << endl;
			APSta.time_idle += SLOT_TIME;

//			cout << "time2: " << sim_time << endl;
		}

		// if only one device won the contention
		else if ((nSenders_ha+nSenders_vi == 1) || ((nSenders_ha==1) && (nSenders_vi==1) && (ha_index==vi_index))) {
			sim_time = sim_time + AIFS_HA;
			nNoCollisions += 1;

			// even if AP wins the contention, need to ensure it has haptic data
			// when only one AC has won
			if (nSenders_ha+nSenders_vi == 1){
				//sta_file << "Only one device" << endl;
				// if AP wins
				if (ap_wins){
					ap_tosend = true;
				}
			}


			// if HA and VI from same STA have won
//			else{
//					// If HA belong to AP
//					for (int y=0; y<nRAStas; y++){
//						if (!pacQ_AP_ha[y].empty()){
//							APhasData=true;
//							break;
//						}
//					}
//
//					if (APSta.bt_ha<0 && APhasData){
//						ap_tosend=true;
//					}
//
//					/***************** Earlier code when VI RTRQ would get updated even when HA-VI of same STA collide *********************/
//					// if STAs have winning VI then CW should be expanded and RTRQ updated
//					for (int z=0; z<nRAStas; z++){
//						if ((RAStas[z].bt_vi<0) && (!pacQ_STA_vi[z].empty())){
//							RAStas[z].sampleCount = pacQ_STA_vi[z].size();
//							RAStas[z].edca_ampdu_len =  std::min(RAStas[z].sampleCount, getEdcaAMpduLength(mcs, bw, MAX_PPDU_DURATION_US, PACKET_SIZE_BWD_VI));
//							RAStas[z].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[z].edca_ampdu_len, PACKET_SIZE_BWD_VI);
//
//							sta_file << "HA senders: " << nSenders_ha << "\tVI senders: " << nSenders_vi << " VI backing off " << endl;
//
//							// do not update retry info if same source HA queue has won
//							//						if (!((pacQ_STA_ha[z].size()>0) && (RAStas[z].bt_ha < 0))){
//							sta_file << z << "\there" << endl;
//							pacQ_holder=&pacQ_STA_vi;
//							retxQ_holder = &retxQ_STA_vi;
//							retry_cnt_holder = &retry_cnt_STA_vi;
//							media = "VI";
//							// call function to update RTRQ table entries
//							AC_packets = updateRetryInfo(z, RAStas[z].edca_ampdu_len-1, RETRY_COUNT_VI, true, sim_time);
//							RAStas[z].dropped_ha += AC_packets.ha;
//							RAStas[z].dropped_vi += AC_packets.vi;
//
//							if (z==0){
//								sta_file << "Dropping " << AC_packets.ha << " haptic and " << AC_packets.vi << " video packets" << endl;
//							}
//							//						}
//
//							// need to inc CW and update RTRQ
//						}
//
//				}

			// if AP alone won the contention
			//no collisions, so simulate an AP transmission
			if (ap_tosend){

				// When AP wins, there should be DL data as it contends only when it has data
				// So initiate DL_OFDMA

				vid_delay_file << "\nNascent stage of DL-OFDMA:    Time: " <<sim_time-AIFS_HA << endl;
//				logging_file << "\nTime: " <<sim_time << "\tAP-success; DL-OFDMA duration: ";
				APSta.max_duration=0;
				APSta.num_dl_STAs=0;
				APSta.dl_stas.clear();
				APSta.dl_stas_ru.clear();
				dl_stas.clear();
				ampdu_DL_currentsize.clear();
				ampdu_DL_currentduration.clear();

				if (nSenders_ha==1){
					// Find if queue is empty or not for each STA
					for (int s=0;s<pacQ_AP_ha.size();s++){
						APSta.queuesize = pacQ_AP_ha[s].size();
						if(APSta.queuesize>0){
							++APSta.num_dl_STAs;
							APSta.dl_stas.push_back(true);
						}
						else{
							APSta.dl_stas.push_back(false);
						}
					}
					pacQ_holder=&pacQ_AP_ha;
					retxQ_holder = &retxQ_AP_ha;
					retry_cnt_holder = &retry_cnt_AP_ha;
					packet_size = PACKET_SIZE_FWD_HA;
					duration = HA_DURATION;
					media = "HA";
					ampdu_len = &ampdu_ap_HA;
					access_ap = &APSta.nSuccAccess_HA;

				}


				if (APSta.num_dl_STAs==1){
					tone=RU_SIZE_996_TONES;
				}
				else if(APSta.num_dl_STAs==2){
					tone=RU_SIZE_484_TONES;
				}
				else if(APSta.num_dl_STAs>=3 && APSta.num_dl_STAs<=4){
					tone=RU_SIZE_242_TONES;
				}
				else if(APSta.num_dl_STAs>=5 && APSta.num_dl_STAs<=8){
					tone=RU_SIZE_106_TONES;
				}
				else if(APSta.num_dl_STAs>=9 && APSta.num_dl_STAs<=18){
					tone=RU_SIZE_52_TONES;
				}

				for(int i=0;i<APSta.dl_stas.size();i++){
					if (APSta.dl_stas[i]){
						APSta.dl_stas_ru.push_back(tone);
					}
					else{
						APSta.dl_stas_ru.push_back(0);
					}
				}

				dl_firsttime = true;


				// Assign RUs for each STA; 0 if empty
				//assignRUs_DL(dl_stas, APSta.num_dl_STAs);

//				cout << "AP: CW -- HA: " << APSta.bt_ha << endl;
//				printf("\n ----------------- DL OFDMA start -- %s \t sim_time: %lld ----------------- \n", media.c_str(), sim_time);
				timeleft = max_ofdma_duration;

				int optimal_queue_dl, highest_sta_dl, optimal_dur_dl, optimal_len_dl, dl_remaining, count_remove_sent_dl=0;
				dl_sampleCount.clear();

				// pair up the buffer sizes and STAs
				if (nSenders_ha==1){
					for (int i = 0; i < nRAStas; i++) {
						if ((*pacQ_holder)[i].size()>0){
							dl_sampleCount.insert(std::pair<int,int>((*pacQ_holder)[i].size(),i));
						}
					}
					delaystemp = &APSta.delaysList.HA;
				}

				else{ // nSenders_vi==1
					for (int i = 0; i < nRAStas; i++) {
						if ((*pacQ_holder)[i].size()>0){
							dl_sampleCount.insert(std::pair<int,int>((*pacQ_holder)[i].size(),i));
						}
					}
					delaystemp = &APSta.delaysList.VI;
				}

				if((dl_sampleCount.size()>0) && (timeleft>40)){
					dlofdma_start_time = sim_time;
				}


//				cout << "No. of STAs: " << dl_sampleCount.size() << "\n";
//				for (auto it=dl_sampleCount.begin(); it!=dl_sampleCount.end(); ++it){
//					cout << it->first << "\t" << it->second << endl;
//				}

				// for multiple DL batches during a media access
				// for single batch during an OFDMA episode, uncomment dl_ofdma_batch
				while((dl_sampleCount.size()>0) && (timeleft>40)){ // && (dl_ofdma_batch==0)
//					vid_delay_file <<  "\n ------ DL OFDMA ----- sim_time:  " << sim_time << endl;
					//++dl_ofdma_batch;
					//dlofdma_interrupted = false;
					// finding the highest buffer and corresponding STA
					for (auto it=dl_sampleCount.rbegin(); it!=dl_sampleCount.rend(); ++it){
						//cout << it->first << "\t" << it->second << "\n" << endl;
						optimal_queue_dl = it->first;
						highest_sta_dl = it->second;
						break;
					}

					nStas_dl = dl_sampleCount.size();

					// HoL frame technique from Magrin's paper

//					ORIGINAL
					if (ofdma_bw_mode){
						if (nStas_dl>=4){
							nDLSTAs = 4;
							dl_remaining = nStas_dl-4;
							tone_dl = RU_SIZE_242_TONES;
						}
						else if(nStas_dl==3){
							nDLSTAs = 3;
							dl_remaining = 0;
							tone_dl = RU_SIZE_242_TONES;
						}
						else if (nStas_dl==2){
							nDLSTAs = 2;
							dl_remaining = 0;
							tone_dl = RU_SIZE_484_TONES;
						}
						else if (nStas_dl==1){
							nDLSTAs = 1;
							dl_remaining = 0;
							tone_dl = RU_SIZE_996_TONES;
						}
					}

					else{
						if (nStas_dl>=8){
//							if (nStas_dl>=16){
//								nDLSTAs = 16;
//								dl_remaining = nStas_dl-16;
//								tone_dl = RU_SIZE_52_TONES;
//							}
//							else if (nStas_dl>8){
								nDLSTAs = 8;
								dl_remaining = 0;
								tone_dl = RU_SIZE_106_TONES;
//							}
						}

						else if (nStas_dl>4){
							nDLSTAs = nStas_dl;
							dl_remaining = 0;
							tone_dl = RU_SIZE_106_TONES;
						}

						if (nStas_dl==4){
							nDLSTAs = 4;
							dl_remaining = 0;
							tone_dl = RU_SIZE_242_TONES;
						}
						else if(nStas_dl==3){
							nDLSTAs = 3;
							dl_remaining = 0;
							tone_dl = RU_SIZE_242_TONES;
						}
						else if (nStas_dl==2){
							nDLSTAs = 2;
							dl_remaining = 0;
							tone_dl = RU_SIZE_484_TONES;
						}
						else if (nStas_dl==1){
							nDLSTAs = 1;
							dl_remaining = 0;
							tone_dl = RU_SIZE_996_TONES;
						}
					}



					// bandwidth utilization scheme from Magrin's paper
//					if (nStas_dl>=9 && nStas_dl<=18){
//						nDLSTAs = nStas_dl;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_52_TONES;
//					}
//					else if (nStas_dl>=5 && nStas_dl<=8){
//						nDLSTAs = nStas_dl;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_106_TONES;
//					}
//					else if (nStas_dl>=3 && nStas_dl<=4){
//						nDLSTAs = nStas_dl;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_242_TONES;
//					}
//					else if (nStas_dl==2){
//						nDLSTAs = 2;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_484_TONES;
//					}
//					else if (nStas_dl==1){
//						nDLSTAs = 1;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_996_TONES;
//					}

//					nStas_dl = dl_sampleCount.size();
//					if (nStas_dl>=4){
//						nDLSTAs = 4;
//						dl_remaining = nStas_dl%4;
//						tone_dl = RU_SIZE_106_TONES;
//					}
//					else if (nStas_dl>=2){
//						nDLSTAs = 2;
//						dl_remaining = nStas_dl%2;
//						tone_dl = RU_SIZE_242_TONES;
//					}
//					else if (nStas_dl==1){
//						nDLSTAs = 1;
//						dl_remaining = 0;
//						tone_dl = RU_SIZE_484_TONES;
//					}

//					cout << "Chosen # STAs: " << nDLSTAs << "\t" << tone_dl << "  timeleft: " << timeleft << "\n";

					optimal_len_dl =  std::min(optimal_queue_dl, getOfdmaAMpduLength(mcs, tone_dl, timeleft, packet_size));
					optimal_dur_dl = getOfdmaAMpduDuration (mcs, tone_dl, 0, 0, optimal_len_dl, packet_size, bw);

					total_length_dl=0;
					for (int k=0; k<nRAStas; k++){
						total_length_dl += pacQ_AP_ha[k].size();
					}
					total_length_dl = total_length_dl*PACKET_SIZE_FWD_HA;

					timeleft = timeleft - (dl_firsttime*(total_length_dl>AP_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) + duration_tf + optimal_dur_dl + SIFS + duration_multi_sta_back);
//					printf("\n Max AMPDU: %d \t max duration: %d\n", optimal_len_dl, optimal_dur_dl);

					batch_dur_file << "DL-OFDMA:\t#STAs: " << nDLSTAs << "\t# frames: " << optimal_len_dl << "\tbatch time: " <<
							RTS_TIME + CTS_TIME + duration_tf + optimal_dur_dl + SIFS + duration_multi_sta_back << endl;
//					nStas_dl_vec.push_back(nDLSTAs);
					sta_file << "DL-OFDMA tx.: time from " << sim_time << " to " ;


					logging_file << sim_time-AIFS_HA << ";";
					sim_time = sim_time + dl_firsttime*(total_length_dl>AP_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) + duration_tf + optimal_dur_dl + SIFS + duration_multi_sta_back;
					logging_file << sim_time << ";" << "AP;K;MU" << endl;
//					logging_file << dl_firsttime*(total_length_dl>AP_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) + optimal_dur_dl + SIFS + duration_multi_sta_back <<
//					 endl;
					if (total_length_dl>AP_RTS_THRESHOLD){
						++rts_cts_count_noCollision;
					}
					++dl_ofdma_access;
					time_overhead += dl_firsttime*(total_length_dl>AP_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) + duration_tf + SIFS + duration_multi_sta_back;
					sta_file << sim_time << endl;
					vid_delay_file << "DL-OFDMA duration: " << optimal_dur_dl <<  endl;

					APSta.time_send +=  dl_firsttime*(total_length_dl>AP_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) + duration_tf + optimal_dur_dl + SIFS + duration_multi_sta_back;
					APSta.time_dataSend += optimal_dur_dl;

					dl_firsttime=false;

					if (nRAStas==4){
						ofdma_track << "STAs " << nRAStas << "\tSTAsData: " << nDLSTAs << "\t#frames: " << optimal_len_dl << "\tdur: " << optimal_dur_dl << "\ttone: " << tone_dl << endl;
					}
					APSta.accessTimeEnd_ha = sim_time;

					// counting the total sim_time spent in DL-OFDMA
					dl_ofdma_tot_dur += optimal_dur_dl;
					//cout << "\nTotal DL duration ---- Prev: " << dl_ofdma_tot_frame-optimal_dur_dl << "\t Now: " << dl_ofdma_tot_dur << endl;

					for (auto rit=dl_sampleCount.rbegin(); rit!=dl_sampleCount.rend(); ++rit){

						stas_dl.push_back(rit->second);

						// tracking the last packet sent
						if (nSenders_ha==1){
							lastSent_temp = &APSta.last_packet_ha[rit->second];
						}


						// # queued packets is less than optimal
						if (rit->first <= optimal_len_dl){
							APSta.apmdu_length.push_back(rit->first);
//							printf("\n AMPDU: %d \t max duration: %d\n", rit->first, optimal_dur_dl);

							dl_ofdma_tot_frame += rit->first;
							//cout << "\nTotal DL frames ---- Prev: " << dl_ofdma_tot_frame-rit->first << "\t Now: " << dl_ofdma_tot_frame << endl;

							if (rit->second == 0){
								dl_zero_ofdma_ampdu += rit->first;
								++dl_zero_ofdma_access;
							}

							APSta.nTx += rit->first;
							++(*access_ap);
							//++APSta.nSuccAccesses;

							(*lastSent_temp)=(*pacQ_holder)[rit->second].back();
							AP_interAccess[rit->second].push_back(sim_time-AP_accessTime[rit->second]);
							AP_accessTime[rit->second] = sim_time;
							APSta_kinFramesSent[rit->second] += rit->first;

							vid_delay_file << "----- DL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << (*pacQ_holder)[rit->second].front() << "\ttime: " <<
																		sim_time << "\tSampleDelays: " ;

							APSta.accessdelay.push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front());
							APSta.ampduLength_kin.push_back(rit->first);
							// recording delays for HA and VI
							for (int z=0;z<rit->first;z++){ //
//								 w/o accounting for jitter buffer delay
								APSta.sampleAccessDelay.push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front()-z*duration);
								// accounting for jitter buffer delay
								(*delaystemp).push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front());
//								printf("AP %d \t Media %s \t sim_time: %d \t Sample: %d, \t AMPDU: %d \t duration: %d \t max_duration: %d \t delay: %d\n",
//										rit->second, media.c_str(), sim_time, (*pacQ_holder)[rit->second].front()+z*duration, rit->first, optimal_dur_dl,
//										optimal_dur_dl, (*delaystemp).back());
								vid_delay_file << APSta.sampleAccessDelay.back() << "   ";

								dl_zero_ofdma_delay.push_back((*delaystemp).back());
								if(ulofdma_just_ap){
									ulofdmadelay_ap.push_back((*delaystemp).back());
								}
								else{
									nonulofdmadelay_ap.push_back((*delaystemp).back());
								}
							}
							vid_delay_file << endl;
							total_kin_frames += rit->first;

							if(ulofdma_just_ap){
								ulofdma_just_ap=false;
							}
							if (rit->second == 0){
								cout << "\n\n --------- sending " << rit->first <<  " packets from " << (*pacQ_holder)[rit->second].front()
												<< " to " << (*pacQ_holder)[rit->second].front()+ (rit->first-1)*1000 << "\n\n" << endl;
							}

							//ap_file <<
							(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+
									rit->first);

							// remove retry details of sent packets
							for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
								if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
									++count_remove_sent_dl;
								}
							}

							(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
									count_remove_sent_dl);
							(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
									count_remove_sent_dl);

							(*ampdu_len) += rit->first;

							--nDLSTAs;
							count_remove_sent_dl=0;
							if (nDLSTAs==0){
								dl_sampleCount.clear();
								break;
							}
						}

						// # queued packets is more than optimal
						else{

							dl_ofdma_tot_frame += optimal_len_dl;

							//cout << "\nTotal DL frames ---- Prev: " << dl_ofdma_tot_frame-optimal_len_dl << "\t Now: " << dl_ofdma_tot_frame << endl;

							APSta.nTx += optimal_len_dl;
							++(*access_ap);
							//++APSta.nSuccAccesses;

							if (rit->second == 0){
								dl_zero_ofdma_ampdu += optimal_len_dl;
								++dl_zero_ofdma_access;
							}

//							printf("\n AMPDU: %d \t max length: %d \t max duration: %d\n", rit->first, optimal_len_dl, optimal_dur_dl);

							(*lastSent_temp)=(*pacQ_holder)[rit->second].front()+(optimal_len_dl-1)*duration;
							AP_interAccess[rit->second].push_back(sim_time-AP_accessTime[rit->second]);
							AP_accessTime[rit->second] = sim_time;
							APSta_kinFramesSent[rit->second] += optimal_len_dl;
							APSta.apmdu_length.push_back(optimal_len_dl);
							APSta.accessdelay.push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front());
							// recording delays for HA and VI

							APSta.ampduLength_kin.push_back(optimal_len_dl);
							for (int z=0;z<optimal_len_dl;z++){ //
//								 w/o accounting for jitter buffer delay
								APSta.sampleAccessDelay.push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front()-z*duration);

								// accounting for jitter buffer delay
								(*delaystemp).push_back(sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front());

//								printf("AP %d \t sim_time: %d \t Sample: %d \t Sample: %d \t AMPDU: %d \t duration: %d \t max_duration: %d \t delay: %d\n",
//										rit->second, sim_time, (*pacQ_holder)[rit->second].front()+z*duration, rit->first, optimal_dur_dl, optimal_dur_dl, (*delaystemp).back());
								dl_zero_ofdma_delay.push_back((*delaystemp).back());

								if(ulofdma_just_ap){
									ulofdmadelay_ap.push_back((*delaystemp).back());
								}
								else{
									nonulofdmadelay_ap.push_back((*delaystemp).back());
								}

							}
							if(ulofdma_just_ap){
								ulofdma_just_ap=false;
							}
							if (rit->second == 0){
								cout << "\n\n --------- sending " << optimal_len_dl <<  " packets from " << (*pacQ_holder)[rit->second].front()
										<< " to " << (*pacQ_holder)[rit->second].front()+(optimal_len_dl-1)*1000 << "\n\n" << endl;
							}

							(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+optimal_len_dl);

							// remove retry details of sent packets
							for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
								if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
									++count_remove_sent_dl;
								}
							}

							(*ampdu_len) += optimal_len_dl;

							(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
									count_remove_sent_dl);
							(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
									count_remove_sent_dl);

							count_remove_sent_dl=0;
							--nDLSTAs;

							total_kin_frames += optimal_len_dl;

							if (nDLSTAs==0){
								dl_sampleCount.clear();
								break;
							}
						}
					}

					// remove sent STAs and go back to DL_OFDMA after first batch if sim_time left
					for (auto it=dl_sampleCount.begin(); it!=dl_sampleCount.end(); ++it){
						if (it->second == stas_dl.back()){
							dl_sampleCount.erase(it, dl_sampleCount.end());
							break;
						}
					}
//					for (auto it=dl_sampleCount.begin(); it!=dl_sampleCount.end(); ++it){
//						std::vector<int>::iterator temp;
//						temp = find (stas_dl.begin(), stas_dl.end(), it->second);
//						if (temp!=stas_dl.end()){
//							dl_sampleCount.erase(it);
//						}
//					}
					stas_dl.clear();
				}

				if(vid_last){
					APSta.interAccess_ha_vid.push_back(sim_time-APSta.lastAccess);
//					if (APSta.interAccess_ha_vid.back()<1500){
//						vid_delay_file << "lower than 1.5 ms" << endl;
//					}
					if (num_collisions==0){
						access_collision_vid_0.push_back(sim_time-APSta.lastAccess);
//						vid_delay_file << "AP --- 0 collision\tinter-access time" << access_collision_0.back() << endl;
					}
					else if (num_collisions==1){
						access_collision_vid_1.push_back(sim_time-APSta.lastAccess);
//						vid_delay_file << "AP --- 0 collision\tinter-access time" << access_collision_0.back() << endl;
					}
					num_collisions=0;
					vid_last=false;
				}
				else{
					APSta.interAccess_ha.push_back(sim_time-APSta.lastAccess);
					if (num_collisions==0){
						access_collision_0.push_back(sim_time-APSta.lastAccess);
						vid_delay_file << "AP --- 0 collision\tinter-access time" << access_collision_0.back() << endl;
					}
					else if (num_collisions>0){
						if (num_collisions==1){
							access_collision_1.push_back(sim_time-APSta.lastAccess);
							vid_delay_file << "AP --- 1 collision\tinter-access time" << access_collision_1.back() << endl;
						}
						else if (num_collisions==2){
							access_collision_2.push_back(sim_time-APSta.lastAccess);
							vid_delay_file << "AP --- 2 collision\tinter-access time" << access_collision_2.back() << endl;
						}
						else if (num_collisions==3){
							access_collision_3.push_back(sim_time-APSta.lastAccess);
							vid_delay_file << "AP --- 3 collision\tinter-access time" << access_collision_3.back() << endl;
						}
						num_collisions=0;
					}
//					if (APSta.interAccess_ha.back()<750){
//						vid_delay_file << "lower than 0.75 ms" << endl;
//					}
//					else if (APSta.interAccess_ha.back()>1500){
//						vid_delay_file << "higher than 1.5 ms" << endl;
//					}
				}
				APSta.interAccess.push_back(sim_time-APSta.lastAccess);
				APSta.lastAccess = sim_time;


				vid_delay_file << "Quitting DL-OFDMA" << endl;
				APSta.cw_ha=0;
				APSta.bt_ha=-1;
				dlofdma_duration.push_back(sim_time-dlofdma_start_time);

				// measuring the buffer occupancy after tx.
				temp_counter_ap=0;
				for (int s=0;s<pacQ_AP_ha.size();s++){
					temp_counter_ap+=pacQ_AP_ha[s].size();
				}
				AP_queuesize.push_back(temp_counter_ap*1.0/pacQ_AP_ha.size());

				++ap_access_counter;

//				Add new STA packets that would have been generated since DL-OFDMA began
//				HA packets
				for (int i = 0; i < nRAStas; i++) {
					if (pacQ_STA_ha[i].empty()){
						last_packet_ha = RAStas[i].lastSent_ha;
					}
					else{
						last_packet_ha = pacQ_STA_ha[i].back();
					}

					if ((sim_time-last_packet_ha)>=HA_DURATION){
						for (int j=1; j<=floor((sim_time-last_packet_ha)*1.0/HA_DURATION); j++){
							pacQ_STA_ha[i].push_back(last_packet_ha+HA_DURATION*j);
							++RAStas[i].generated_ha;
						}
					}

					if (pacQ_STA_ha[i].size()>buffer_limit){
						vid_delay_file << "STA-" << i<<  "\tQueue spill-over dropping " << pacQ_STA_ha[i].size()-buffer_limit << endl;
						RAStas[i].dropped_ha += (pacQ_STA_ha[i].size()-buffer_limit);
						pacQ_STA_ha[i].erase(pacQ_STA_ha[i].begin(), pacQ_STA_ha[i].begin()+
								pacQ_STA_ha[i].size()-buffer_limit);

					}
				}


				for (int i = 0; i < nRAStas; i++) {
					if (pacQ_STA_vi[i].empty()){
						last_packet_vi = RAStas[i].lastSent_vi;
					}
					else{
						last_packet_vi = pacQ_STA_vi[i].back();
					}

					//			vid_delay_file << "sim_time: " << sim_time << "\tLastPacket: " << last_packet_vi << endl;
					if ((sim_time-last_packet_vi)>=VI_DURATION){ // assuming the video sampling rate is 60Hz

						// frame generation
						for (int j=1; j<=floor((sim_time-last_packet_vi)*1.0/VI_DURATION); j++){
							packet_size_vi = (PACKET_SIZE_BWD_VI);// + ((rand() % 9)-4)*FRAGMENT_SIZE; // packet size \in [15000, 25000]
							pacQ_STA_vi_size[i].push_back(int(packet_size_vi*1.0/FRAGMENT_SIZE));
							//					temp_file << "STA: " << i << "\ttime: " << sim_time << "\tPacketSize: " << packet_size_vi << endl;
							// fragment generation
							for (int x=0;x<int(packet_size_vi*1.0/FRAGMENT_SIZE); x++){
								pacQ_STA_vi[i].push_back(last_packet_vi+VI_DURATION*j);
							}
							temp_file << "FrameTime: " << last_packet_vi+VI_DURATION*j << "\tSTA: " << i << "\t#Fragments: " << int(packet_size_vi*1.0/FRAGMENT_SIZE) << endl;
							++RAStas[i].generated_vi;
							vid_delay_file << "Time: " << sim_time << "\tVid frames generated: " << RAStas[i].generated_vi << endl;
						}
					}
				}


//				VI packets
//				for (int i = 0; i < nRAStas; i++) {
//					if (pacQ_STA_vi[i].empty()){
//						last_packet_vi = RAStas[i].lastSent_vi;
//					}
//					else{
//						last_packet_vi = pacQ_STA_vi[i].back();
//					}
//
//					if ((sim_time-pacQ_STA_vi[i].back())>=VI_DURATION){
//						for (int j=1; j<=floor((sim_time-last_packet_vi)*1.0/VI_DURATION); j++){
//							pacQ_STA_vi[i].push_back(last_packet_vi+VI_DURATION*j);
//							++RAStas[i].generated_vi;
//						}
//					}
//				}

//				Add new STA packets that would have been generated since DL-OFDMA began
//				HA packets
//				for (int i = 0; i < nRAStas; i++) {
//					if (pacQ_STA_ha[i].empty()){
//						last_packet_ha = RAStas[i].lastSent_ha;
//					}
//					else{
//						last_packet_ha = pacQ_STA_ha[i].back();
//					}
//
//					if ((sim_time-pacQ_STA_ha[i].back())>=HA_DURATION){
//						//cout << "---------- STA: " << i << "\tTime: " << sim_time << "\tQ-back: " << last_packet << endl;
//						for (int j=1; j<=floor((sim_time-last_packet_ha)*1.0/HA_DURATION); j++){
//							pacQ_STA_ha[i].push_back(last_packet_ha+HA_DURATION*j);
//							++RAStas[i].generated_ha;
//						}
//						//cout << "---------- Adding " << floor((sim_time-last_packet)*1.0/1000.0) << " packets\t" << "Q-back: " << packetQueue_STA[i].back() << endl;
//					}
//
//				}
//
//				// VI packets
//				for (int i = 0; i < nRAStas; i++) {
//					if (pacQ_STA_vi[i].empty()){
//						last_packet_vi = RAStas[i].lastSent_vi;
//					}
//					else{
//						last_packet_vi = pacQ_STA_vi[i].back();
//					}
//
//					if ((sim_time-pacQ_STA_vi[i].back())>=VI_DURATION){
//						//cout << "---------- STA: " << i << "\tTime: " << sim_time << "\tQ-back: " << last_packet << endl;
//						for (int j=1; j<=floor((sim_time-last_packet_vi)*1.0/VI_DURATION); j++){
//							pacQ_STA_vi[i].push_back(last_packet_vi+VI_DURATION*j);
//							++RAStas[i].generated_vi;
//						}
//						//cout << "---------- Adding " << floor((sim_time-last_packet)*1.0/1000.0) << " packets\t" << "Q-back: " << packetQueue_STA[i].back() << endl;
//					}
//				}

//				txtime_ap.push_back(APSta.max_duration);

				//APSta.max_bt=0;

				APSta.dl_stas.clear();
				APSta.dl_stas_ru.clear();
				APSta.current_size.clear();

				ul_sampleCount.clear();
				int optimal_queue_ul, highest_sta_ul, optimal_dur_ul, optimal_len_ul, ul_remaining, count_remove_sent_ul=0, max_len_ul, max_len_ul_batch, hap_len_highest_sta,
						optimal_len_hv_ul, hap_len_sta, haptic_dur_ul_max=0;

				vi_empty = true;
				ha_empty = true;
				for (int i = 0; i < nRAStas; i++) {
					if (pacQ_STA_vi[i].size()>0){
						vi_empty = false;
						break;
					}
				}
				for (int i = 0; i < nRAStas; i++) {
					if (pacQ_STA_ha[i].size()>0){
						ha_empty = false;
						break;
					}
				}

//				if (!vi_empty){
//					++ha_ulofdma;
//				}
//				else{
//					ha_ulofdma=0;
//					++vi_empty_counter;
//				}


				ul_sampleCount.clear();
				// Choose HA and VI alternatively during each UL-OFDMA episode
				// When VI is chosen, apply multi-TID
				/********** COMMENT THIS FOR HETEROGENEOUS *********/
				if (vi_empty && !ha_empty){ // ha_ulofdma%3!=0
					vid_delay_file << "------- HA in UL-OFDMA -------" << endl;
					ofdma_track_file << "Time: " << floor(sim_time*1.0/1000) << "\t" << ap_access_counter << "-th AP access\t" <<  "Vid Q empty: " << vi_empty
							<< "\tHA chosen: " << ha_ulofdma << endl;
					// pair up the buffer sizes and STAs
					for (int i = 0; i < nRAStas; i++) {
						if (pacQ_STA_ha[i].size()>0){
							ul_sampleCount.insert(std::pair<int,int>(pacQ_STA_ha[i].size(),i));
						}
					}
					if((ul_sampleCount.size()>8)){

					}
					pacQ_holder = &pacQ_STA_ha;
					retxQ_holder = &retxQ_STA_ha;
					retry_cnt_holder = &retry_cnt_STA_ha;
					packet_size = PACKET_SIZE_BWD_HA;
					duration = HA_DURATION;
					media = "HA";
					++ha_ulofdma_episode;
				}

				else if (!vi_empty){
					vid_delay_file << "------- VI in UL-OFDMA -------" << endl;
					ofdma_track_file << "Time: " << floor(sim_time*1.0/1000) << ap_access_counter << "-th AP access\t" <<  "Vid Q empty: " << vi_empty << "\tVI chosen: "
							<< ha_ulofdma << endl;
					vi_stas = 0;
					ha_only_stas = 0;
					// pair up the buffer sizes and STAs
					for (int i = 0; i < nRAStas; i++) {
						if (pacQ_STA_vi[i].size()>0){
//							ul_sampleCount.insert(std::pair<int,int>(pacQ_STA_vi[i].size()*FRAGMENT_SIZE+pacQ_STA_ha[i].size()*PACKET_SIZE_BWD_HA,i));
							int temper;
							if (pacQ_STA_vi[i].size()*FRAGMENT_SIZE < PACKET_SIZE_BWD_VI*fragment_threshold){
								temper = pacQ_STA_vi[i].size()*FRAGMENT_SIZE;
							}
							else{
								temper = PACKET_SIZE_BWD_VI*fragment_threshold;
							}
//							int temper=min(pacQ_STA_vi[i].size()*FRAGMENT_SIZE,PACKET_SIZE_BWD_VI*fragment_threshold);
							ul_sampleCount.insert(std::pair<int,int>(temper+pacQ_STA_ha[i].size()*PACKET_SIZE_BWD_HA,i));
							++vi_stas;
						}
						else{
							if (pacQ_STA_ha[i].size()>0){
								ul_sampleCount.insert(std::pair<int,int>(pacQ_STA_ha[i].size()*PACKET_SIZE_BWD_HA,i));
								++ha_only_stas;
								vid_delay_file << "****** STA: " << i << " has no VI fragment but has HA frames" << endl;
							}
						}
					}


					for (auto rit=ul_sampleCount.rbegin(); rit!=ul_sampleCount.rend(); ++rit){
						vid_delay_file << "STA-" << rit->second << "\tSize: " << rit->first << endl;
					}


					if(ul_sampleCount.size()>0){
						pacQ_holder = &pacQ_STA_vi;
						pacQ_size_holder = &pacQ_STA_vi_size;
						retxQ_holder = &retxQ_STA_vi;
						retry_cnt_holder = &retry_cnt_STA_vi;
						packet_size = FRAGMENT_SIZE;
						duration = VI_DURATION;
						media = "VI";
						for (int i = 0; i < nRAStas; i++) {
							RAStas[i].ulofdma_just_sta = true;
						}
						ulofdma_just_ap = true;
						++vi_ulofdma_episode;
					}
					else{
						vid_delay_file << "Chose VI but no frames to send" << endl;
					}
				}

				if((ul_sampleCount.size()>0) && (timeleft>40)){
					ulofdma_start_time = sim_time;
					vid_delay_file << "OFDMA start time: " << ulofdma_start_time/1000.0 << endl;
					ul_firsttime = true;
				}



				//								multi-TID part
				//								add haptic samples generated after triggering DL-OFDMA
//													for (int i = 0; i < nRAStas; i++) {
//														if (pacQ_STA_ha[i].empty()){
//															last_packet_ha = RAStas[i].lastSent_ha;
//														}
//														else{
//															last_packet_ha = pacQ_STA_ha[i].back();
//														}
//
//														if ((sim_time-last_packet_ha)>=HA_DURATION){
//															//cout << "---------- STA: " << i << "\tTime: " << sim_time << "\tQ-back: " << last_packet << endl;
//															for (int j=1; j<=floor((sim_time-last_packet_ha)*1.0/HA_DURATION); j++){
//																pacQ_STA_ha[i].push_back(last_packet_ha+HA_DURATION*j);
//																++RAStas[i].generated_ha;
//															}
//														}
//													}

 				// Trigger MU-UL transmissions if feasible
//					while((ul_sampleCount.size()>0) && (timeleft>40)){ // && (ul_ofdma_batch==0)
//				logging_file << "Time: " <<sim_time << "\tAP-success; UL-OFDMA duration: ";
				inside_ulofdma = false;
				while((ul_sampleCount.size()>0) && (timeleft>40)){
						//++ul_ofdma_batch;
						//printf("\n ----------------- UL OFDMA start -- %s ----------------- \n", media.c_str());

						vid_delay_file << "Entering UL-OFDMA!!  time:  " << sim_time << "\ttime left: " << timeleft;
						inside_ulofdma = true;
						// finding the highest buffer and corresponding STA
						auto it=ul_sampleCount.rbegin();
						optimal_queue_ul = it->first;
						highest_sta_ul = it->second;
						++it;
						while(it!=ul_sampleCount.rend()){
							if (pacQ_STA_vi[it->second].size()<optimal_queue_ul){
								break;
							}
							else{
								if (pacQ_STA_ha[it->second].size()>pacQ_STA_ha[highest_sta_ul].size()){
									optimal_queue_ul = it->first;
									highest_sta_ul = it->second;
								}
								++it;
							}
						}

//						for (auto it=ul_sampleCount.rbegin(); it!=ul_sampleCount.rend(); ++it){
////							cout << it->first << "\t" << it->second << "\n" << endl;
//
//
//
////							if (!vi_empty){
////								optimal_queue_ul = it->first;
////							}
//							break;
//						}

						vid_delay_file << "\nBT_HA of STAs" << endl;
						for (int i = 0; i < nRAStas; i++) {
							vid_delay_file << "STA-" << i << "\tBT_HA: " << RAStas[i].bt_ha << "\tCW: " << RAStas[i].cw_ha << "\tQ-size: " <<
									pacQ_STA_ha[i].size() << endl;
						}

//						vid_delay_file << "STA: 1\t #fragments: " << pacQ_STA_vi[0].size() << "\tFrameSize: " << pacQ_STA_vi_size[0].front() << endl;

						nStas_ul = ul_sampleCount.size();
						vid_delay_file << "No. of STAs with data: " << nStas_ul << endl;

						if (media.compare("HA")==0){
							// HoL frame technique
//							ORIGINAL
							if (ofdma_bw_mode){
								if (nStas_ul>=4){
									nULSTAs = 4;
									ul_remaining = nStas_ul-4;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if(nStas_ul==3){
									nULSTAs = 3;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if (nStas_ul==2){
									nULSTAs = 2;
									ul_remaining = 0;
									tone_ul = RU_SIZE_484_TONES;
								}
								else if (nStas_ul==1){
									nULSTAs = 1;
									ul_remaining = 0;
									tone_ul = RU_SIZE_996_TONES;
								}
							}


							else {
								if (nStas_ul>=8){
//									if (nStas_ul>=16){
//										nULSTAs = 16;
//										ul_remaining = nStas_ul-16;
//										tone_ul = RU_SIZE_52_TONES;
//									}
//									else if (nStas_ul>8){
										nULSTAs = 8;
										ul_remaining = 0;
										tone_ul = RU_SIZE_106_TONES;
//									}
								}

								else if (nStas_ul>4){
									nULSTAs = nStas_ul;
									ul_remaining = 0;
									tone_ul = RU_SIZE_106_TONES;
								}

								//							if (nStas_ul>=8){
								//								nULSTAs = 8;
								//								ul_remaining = nStas_ul-8;
								//								tone_ul = RU_SIZE_106_TONES;
								//							}
								else if (nStas_ul==4){
									nULSTAs = 4;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if(nStas_ul==3){
									nULSTAs = 3;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if (nStas_ul==2){
									nULSTAs = 2;
									ul_remaining = 0;
									tone_ul = RU_SIZE_484_TONES;
								}
								else if (nStas_ul==1){
									nULSTAs = 1;
									ul_remaining = 0;
									tone_ul = RU_SIZE_996_TONES;
								}
							}
						}

						else{


//							ORIGINAL
							if (ofdma_bw_mode){
								if (nStas_ul>=4){
									nULSTAs = 4;
									ul_remaining = nStas_ul-4;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if(nStas_ul==3){
									nULSTAs = 3;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if (nStas_ul==2){
									nULSTAs = 2;
									ul_remaining = 0;
									tone_ul = RU_SIZE_484_TONES;
								}
								else if (nStas_ul==1){
									nULSTAs = 1;
									ul_remaining = 0;
									tone_ul = RU_SIZE_996_TONES;
								}
							}


							else{
								if (nStas_ul>=8){
//									if (nStas_ul>=16){
//										nULSTAs = 16;
//										ul_remaining = nStas_ul-16;
//										tone_ul = RU_SIZE_52_TONES;
//									}
//									else if (nStas_ul>8){
										nULSTAs = 8;
										ul_remaining = 0;
										tone_ul = RU_SIZE_106_TONES;
//									}
								}

								else if (nStas_ul>4){
									nULSTAs = nStas_ul;
									ul_remaining = 0;
									tone_ul = RU_SIZE_106_TONES;
								}
								//							if (nStas_ul>=8){
								//								nULSTAs = 8;
								//								ul_remaining = nStas_ul-8;
								//								tone_ul = RU_SIZE_106_TONES;
								//							}
								if (nStas_ul==4){
									nULSTAs = 4;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if(nStas_ul==3){
									nULSTAs = 3;
									ul_remaining = 0;
									tone_ul = RU_SIZE_242_TONES;
								}
								else if (nStas_ul==2){
									nULSTAs = 2;
									ul_remaining = 0;
									tone_ul = RU_SIZE_484_TONES;
								}
								else if (nStas_ul==1){
									nULSTAs = 1;
									ul_remaining = 0;
									tone_ul = RU_SIZE_996_TONES;
								}
							}
						}



						vid_delay_file << "\nSelecting " << nULSTAs << " STAs" << "\tSTA-" << highest_sta_ul << "\tSend Q size: " << ul_sampleCount.size() << endl;

						// bandwidth utilization
//						if (nStas_ul>=9 && nStas_ul<=18){
//							nULSTAs = nStas_ul;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_52_TONES;
//						}
//						else if (nStas_ul>=5 && nStas_ul<=8){
//							nULSTAs = nStas_ul;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_106_TONES;
//						}
//						else if (nStas_ul>=3 && nStas_ul<=4){
//							nULSTAs = nStas_ul;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_242_TONES;
//						}
//						else if (nStas_ul==2){
//							nULSTAs = 2;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_484_TONES;
//						}
//						else if (nStas_ul==1){
//							nULSTAs = 1;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_996_TONES;
//						}

//						nStas_ul = ul_sampleCount.size();
//						if (nStas_ul>=4){
//							nULSTAs = 4;
//							ul_remaining = nStas_ul%4;
//							tone_ul = RU_SIZE_106_TONES;
//						}
//						else if (nStas_ul>=2){
//							nULSTAs = 2;
//							ul_remaining = nStas_ul%2;
//							tone_ul = RU_SIZE_242_TONES;
//						}
//						else if (nStas_ul==1){
//							nULSTAs = 1;
//							ul_remaining = 0;
//							tone_ul = RU_SIZE_484_TONES;
//						}

//						cout << "Chosen # UL STAs: " << nULSTAs << "\t" << tone_ul << "timeleft: " << timeleft << "\n";

						max_len_ul = getOfdmaAMpduLength(mcs, tone_ul, timeleft, PACKET_SIZE_BWD_HA);

//						haptic tx.
						if (!ha_empty && vi_empty){
							optimal_len_ul =  std::min(optimal_queue_ul, getOfdmaAMpduLength(mcs, tone_ul, timeleft, PACKET_SIZE_BWD_HA));
							optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, 0, 0, optimal_len_ul, PACKET_SIZE_BWD_HA, bw);
							total_length_ul = optimal_len_ul*PACKET_SIZE_BWD_HA;
						}
//						else if(!vi_empty){
//							optimal_len_ul =  std::min(optimal_queue_ul, getOfdmaAMpduLength(mcs, tone_ul, timeleft, packet_size));
//							vid_delay_file << "Optimal length: " << optimal_len_ul << endl;
//							optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_ul, packet_size, bw);
//
//						}
//						ul_ofdma_data.push_back(optimal_dur_ul);
//						ul_ofdma_overhead.push_back(RTS_TIME + CTS_TIME + duration_tf + SIFS + SIFS + duration_multi_sta_back);

//						video tx.
						else if (!vi_empty){
							vid_delay_file << "No. of -- VI STAs: " << vi_stas << "\tHA STAs: " << ha_only_stas << endl;
//							if there is atleast 1 VI STA
							if (vi_stas>0){
								vid_last=true;
								if (!ha_empty){
									highest_sta_hap_size=pacQ_STA_ha[highest_sta_ul].size();
									optimal_dur_ul = std::min(timeleft, getOfdmaAMpduDuration (mcs, tone_ul, 1, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw));
									//								not all haptic frames can go
									if (optimal_dur_ul==timeleft){
										vid_delay_file << "Can send 1 VI frame and partial HA frames" << endl;
										while(optimal_dur_ul>=timeleft){
											optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, 1, FRAGMENT_SIZE, --highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
										}
										vid_delay_file << "Can send 1 VI frame and " << highest_sta_hap_size << " HA frames" << endl;
										total_length_ul = 1*FRAGMENT_SIZE+highest_sta_hap_size*PACKET_SIZE_BWD_HA;
										hap_frame_length = highest_sta_hap_size;
										vid_fragment_length = 1;
									}

									//								all haptic frames can be sent; find out how many VI frames can be sent
									else{
										vid_delay_file << "Can send all all/some VI frames and HA frames" << endl;
										vid_frames = 0;
										vid_exhausted=false;
										while ((optimal_dur_ul<timeleft)){
											optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, ++vid_frames, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
											if ((vid_frames>=pacQ_STA_vi[highest_sta_ul].size())){
												vid_exhausted=true;
												break;
											}
										}
										vid_delay_file << "At the time of exiting loop, we have " << vid_frames << " VI frames" << endl;
										if (!vid_exhausted){
											vid_frames = min(--vid_frames, fragments_per_frame);
											optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, vid_frames, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
											vid_delay_file << "Can send " << vid_frames << " VI frame and " << highest_sta_hap_size << " HA frames" << endl;
											total_length_ul = vid_frames*FRAGMENT_SIZE+highest_sta_hap_size*PACKET_SIZE_BWD_HA;
											hap_frame_length = highest_sta_hap_size;
											vid_fragment_length = vid_frames;
										}
										else{
											vid_frames = min(vid_frames, fragments_per_frame);
											optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, vid_frames, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
											vid_delay_file << "Can send " << vid_frames << " VI frames and " << highest_sta_hap_size << " HA frames" << endl;
											total_length_ul = vid_frames*FRAGMENT_SIZE+highest_sta_hap_size*PACKET_SIZE_BWD_HA;
											hap_frame_length = highest_sta_hap_size;
											vid_fragment_length = vid_frames;
										}

									}

									vid_delay_file << "Optimal duration: " << optimal_dur_ul << endl;
								}
								else{
									optimal_dur_ul = std::min(timeleft, getOfdmaAMpduDuration (mcs, tone_ul, min(fragments_per_frame,optimal_queue_ul), FRAGMENT_SIZE, 0, 0, bw));
									if (optimal_dur_ul==timeleft){
										optimal_len_ul = getOfdmaAMpduLength(mcs, tone_ul, timeleft, FRAGMENT_SIZE);
										optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_ul, FRAGMENT_SIZE, 0, 0, bw);
										vid_delay_file << "Highest STA cannot send HA frames" << endl;
										total_length_ul = optimal_len_ul*FRAGMENT_SIZE;
										hap_frame_length = 0;
										vid_fragment_length = optimal_len_ul;
									}
									else{
										highest_sta_hap_size=pacQ_STA_ha[highest_sta_ul].size();
										optimal_len_ul = min(fragments_per_frame,optimal_queue_ul);
										optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_ul, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
										while (optimal_dur_ul>timeleft){
											optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_ul, FRAGMENT_SIZE, --highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw);
										}
										vid_delay_file << "Highest STA" << highest_sta_ul << " can send " << highest_sta_hap_size << " HA frames" << endl;
										total_length_ul = optimal_len_ul*FRAGMENT_SIZE+highest_sta_hap_size*PACKET_SIZE_BWD_HA;
										hap_frame_length = highest_sta_hap_size;
										vid_fragment_length = optimal_len_ul;
									}
									vid_delay_file << "Optimal duration: " << optimal_dur_ul << endl;
								}
							}
//							if there are only HA STAs
							else if (ha_only_stas>0){
//								vid_delay_file << "uncertain stage" << endl;
								highest_sta_hap_size=pacQ_STA_ha[highest_sta_ul].size();
								optimal_dur_ul = std::min(timeleft, getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw));
								if (optimal_dur_ul==timeleft){
									while(optimal_dur_ul>=timeleft){
										optimal_dur_ul = std::min(timeleft, getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, --highest_sta_hap_size, PACKET_SIZE_BWD_HA, bw));
									}
								}
								total_length_ul = highest_sta_hap_size*PACKET_SIZE_BWD_HA;
							}

						}


//						else if (!vi_empty){
//							max_len_ul = getOfdmaAMpduLength(mcs, tone_ul, timeleft, PACKET_SIZE_BWD_HA);
//							vid_delay_file << "Max sendable length (in terms of 240B): " << max_len_ul << endl;
//							optimal_len_ul =  std::min(optimal_queue_ul, getOfdmaAMpduLength(mcs, tone_ul, timeleft, packet_size));
//							vid_delay_file << "Video optimal length: " << optimal_len_ul << endl;
//							hap_len_highest_sta = pacQ_STA_ha[highest_sta_ul].size();
//							vid_delay_file << "Highest haptic length: " << hap_len_highest_sta << endl;
//							vid_delay_file << "Total: " << hap_len_highest_sta+(optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA) << endl;
////							if all HA data can be sent for sta with highest VI data
//							if (hap_len_highest_sta+optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA <= max_len_ul){
//								optimal_len_hv_ul = hap_len_highest_sta+ceil(optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA);
//								vid_delay_file << "STA: " << highest_sta_ul << "  has " << pacQ_STA_ha[highest_sta_ul].size() << " frames and can send " <<
//										hap_len_highest_sta << " haptic frames" << endl;
//								vid_delay_file << "Haptic-Video optimal length (in terms of 240B): " << optimal_len_hv_ul << endl;
//								optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_hv_ul, PACKET_SIZE_BWD_HA, bw);
//							}
////							not all HA data can be sent for sta with highest VI data
//							else{
////								atleast 1 HA data can be sent?
//								if (optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA <= max_len_ul){
//									hap_len_highest_sta = max_len_ul-ceil(optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA);
//									optimal_len_hv_ul = hap_len_highest_sta+ceil(optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA);
//									vid_delay_file << "STA: " << highest_sta_ul << "  has " << pacQ_STA_ha[highest_sta_ul].size() << " frames but can send only" <<
//											hap_len_highest_sta << " haptic frames" << endl;
//									vid_delay_file << "Haptic-Video optimal length (in terms of 240B): " << optimal_len_hv_ul << endl;
//									optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_hv_ul, PACKET_SIZE_BWD_HA, bw);
//								}
////								no HA data can be sent
//								else{
//									vid_delay_file << "STA: " << highest_sta_ul << "  cannot send any haptic frames " << endl;
//									optimal_len_hv_ul = ceil(optimal_len_ul*packet_size*1.0/PACKET_SIZE_BWD_HA);
//									vid_delay_file << "Haptic-Video optimal length (in terms of 1375B): " << optimal_len_hv_ul << endl;
//									optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_hv_ul, PACKET_SIZE_BWD_HA, bw);
//								}
//
//							}
//
//							vid_delay_file << "Optimal duration: " << optimal_dur_ul << endl;
//
//						}

						vid_delay_file << "batch time: " << optimal_dur_ul << endl;
						if (total_length_ul>STA_RTS_THRESHOLD){
							++rts_cts_count_noCollision;
						}
						timeleft = timeleft - (ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back); // (total_length_ul>RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
//						printf("\n Max AMPDU: %d \t max duration: %d\n", optimal_len_ul, optimal_dur_ul);
						vid_delay_file << "Time just before updating: " << sim_time << "\tadding: " << ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back << endl;
//						logging_file << sim_time << ";" ;
						sim_time = sim_time + bsrptime + SIFS + bsrtime + ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back; // (total_length_ul>RTS_THRESHOLD)*(RTS_TIME + CTS_TIME)

						if (total_length_ul>STA_RTS_THRESHOLD){
							++rts_cts_count_noCollision;
						}

						++ul_ofdma_access;

						time_overhead += ul_firsttime*duration_tf + SIFS + SIFS + duration_multi_sta_back; // (total_length_ul>RTS_THRESHOLD)*(RTS_TIME + CTS_TIME)
						ul_ofdma_dur.push_back(ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back); // (total_length_ul>RTS_THRESHOLD)*(RTS_TIME + CTS_TIME)

						vid_delay_file << "Time: " << sim_time << endl;
//						cout << "time4: " << sim_time << endl;
						APSta.time_staSend += ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back; // (total_length_ul>RTS_THRESHOLD)*(RTS_TIME + CTS_TIME)
						APSta.time_staDataSend += optimal_dur_ul;

						ul_firsttime=false;

						// counting the total sim_time spent in UL-OFDMA
						ul_ofdma_tot_dur += optimal_dur_ul;
						//cout << "\nTotal UL duration ---- Prev: " << ul_ofdma_tot_frame-optimal_dur_ul << "\t Now: " << ul_ofdma_tot_dur << endl;

						vid_delay_file << "Highest sta index: " << highest_sta_ul << endl;

						for (auto rit=ul_sampleCount.rbegin(); rit!=ul_sampleCount.rend(); ++rit){


							//++RAStas[rit->second].nSuccAccesses_mu;
							stas_ul.push_back(rit->second);

							// tracking the last packet sent
							/********** COMMENT THIS FOR HETEROGENEOUS *********/
//							if ((ha_ulofdma%p!=0)){ // ha_ulofdma%3!=0
							if(!ha_empty && vi_empty){
								vid_delay_file << "inside HA" << endl;
								lastSent_temp = &RAStas[rit->second].lastSent_ha;
								delaystemp=&RAStas[rit->second].delaysList.HA;
								delays_mu=&RAStas[rit->second].delays_mu.HA;
								delays_su=&RAStas[rit->second].delays_su.HA;
								accesstemp = &RAStas[rit->second].nSuccAccess_HA;
								//accesstemp_su = &RAStas[rit->second].nSuccAccess_su_HA;
								accesstemp_mu = &RAStas[rit->second].nSuccAccess_mu_HA;
								ampdu_len = &ampdu_sta_mu_HA;
							}
							else if (!vi_empty){
								vid_delay_file << "inside VI" << endl;
								lastSent_temp = &RAStas[rit->second].lastSent_vi;
								delaystemp=&RAStas[rit->second].delaysList.VI;
								delays_mu=&RAStas[rit->second].delays_mu.VI;
								delays_su=&RAStas[rit->second].delays_su.VI;
								accesstemp = &RAStas[rit->second].nSuccAccess_VI;
								//accesstemp_su = &RAStas[rit->second].nSuccAccess_su_VI;
								accesstemp_mu = &RAStas[rit->second].nSuccAccess_mu_VI;
								ampdu_len = &ampdu_sta_mu_VI;
							}
//							vid_delay_file <<  "\n ------ UL-OFDMA access ----- sim_time:  " << sim_time << endl;

							vi_fragments=0;
							ha_frames=0;
							if (!vi_empty){
								if (!pacQ_STA_vi[rit->second].empty()){

									vi_fragments = 1;
									ha_frames = pacQ_STA_ha[rit->second].size();
								}
								else if (!pacQ_STA_ha[rit->second].empty()){
									vi_fragments = 0;
									ha_frames = pacQ_STA_ha[rit->second].size();
								}
								if(ha_frames>0){
									RAStas[rit->second].haptic_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw);
									RAStas[rit->second].haptic_dur_ul_delay = getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, 1, PACKET_SIZE_BWD_HA, bw);
									vid_delay_file << "Total UL duration: " << optimal_dur_ul << "\thaptic UL duration: " << RAStas[rit->second].haptic_dur_ul << endl;
									if (RAStas[rit->second].haptic_dur_ul>haptic_dur_ul_max)
										haptic_dur_ul_max = RAStas[rit->second].haptic_dur_ul;
								}
							}
							else if (!ha_empty && vi_empty){
								vi_fragments = 0;
								ha_frames = pacQ_STA_ha[rit->second].size();
								RAStas[rit->second].haptic_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw);
								RAStas[rit->second].haptic_dur_ul_delay = getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, 1, PACKET_SIZE_BWD_HA, bw);
								vid_delay_file << "Total UL duration: " << optimal_dur_ul << "\thaptic UL duration: " << RAStas[rit->second].haptic_dur_ul << endl;
								if (RAStas[rit->second].haptic_dur_ul>haptic_dur_ul_max)
									haptic_dur_ul_max = RAStas[rit->second].haptic_dur_ul;
							}


//							******** START HERE TO IMPLEMENT NEW ALGORITHM WHERE ATLEAST 1 VI AND ALL/SOME HA FRAMES ARE TO BE TRANSMITTED ********

							if (getOfdmaAMpduDuration (mcs, tone_ul, vi_fragments, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){
								if (!vi_empty){
									if (!pacQ_STA_vi[rit->second].empty()){
										--vi_stas;
									}
									else if (!pacQ_STA_ha[rit->second].empty()){
										--ha_only_stas;
										vid_delay_file << "Only HA frames here as no VI frames queued up" << endl;
									}
									while ((getOfdmaAMpduDuration (mcs, tone_ul, ++vi_fragments, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw) <= optimal_dur_ul)){
										if ((vi_fragments>pacQ_STA_vi[rit->second].size())){
											vid_exhausted=true;
											break;
										}
									}
									vid_delay_file << "Initially selected " << vi_fragments << " VI frames" << endl;
									--vi_fragments;
									vid_delay_file << "Then decremented to " << vi_fragments << " VI frames" << endl;
									vi_fragments = min(vi_fragments, fragments_per_frame);
									vid_delay_file << "After min(), selecting " << vi_fragments << " VI frames" << endl;
//									optimal_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, vi_fragments, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw);

									if (!pacQ_STA_vi[rit->second].empty()){
										ul_ofdma_tot_frame += rit->first*1.0/FRAGMENT_SIZE;
										//								cout << "\nTotal UL frames ---- Prev: " << ul_ofdma_tot_frame-rit->first << "\t Now: " << ul_ofdma_tot_frame << endl;
										RAStas[rit->second].nTx += rit->first*1.0/FRAGMENT_SIZE;
										RAStas[rit->second].fragments_sent += vi_fragments;
										(*lastSent_temp)=(*pacQ_holder)[rit->second][vi_fragments-1]; //+(rit->first-1)*duration;
									}

									if (!pacQ_STA_vi[rit->second].empty()){
										if (RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
											num_frames_sent=0;
											//									vid_delay_file << "#FragmentsSent: " << RAStas[rit->second].fragments_sent << "\tQ-sizeFront: " << (*pacQ_size_holder)[rit->second].front() << endl;
											while(RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
												vid_delay_file << endl ;
												++RAStas[rit->second].frames_sent;
												++RAStas[rit->second].vid_frames_sent;
												++num_frames_sent;
												// record video delays
												// w/o accounting for jitter buffer
												RAStas[rit->second].sampleAccessDelayVid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION)));

												// accounting for jitter buffer
												(*delaystemp).push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))+(num_frames_sent-1)*VI_DURATION);
												//										delay_vid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))/1000.0);
												vid_delay_file << "STA: " << rit->second << "\t" << RAStas[rit->second].frames_sent-1 << "\t" <<
														(RAStas[rit->second].frames_sent-1)*VI_DURATION/1000.0 << "\t" << sim_time << "\t" << (*delaystemp).back() << "\tQueued: " << rit->first
														<<  "\t#sent: " << RAStas[rit->second].fragments_sent ;

												RAStas[rit->second].fragments_sent = RAStas[rit->second].fragments_sent-(*pacQ_size_holder)[rit->second].front();
												(*pacQ_size_holder)[rit->second].erase((*pacQ_size_holder)[rit->second].begin(), (*pacQ_size_holder)[rit->second].begin()+1);

											}


											vid_delay_file << "\tspill-over: " << RAStas[rit->second].fragments_sent <<  "\tUL-OFDMA: " << rit->first << "\topt: " << optimal_len_ul
													<< "\tUL-OFDMA<opt" << endl;


										}

										else{
											vid_delay_file << "-----------INCOMPLETE FRAME TRANSMISSION----------" << endl;
											vid_delay_file <<  "STA: " << rit->second << "\tspill-over" << RAStas[rit->second].fragments_sent << "\tFrameSize: " << (*pacQ_size_holder)[rit->second].front()
																										<< "\tUL-OFDMA<opt" << endl;
										}



										(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+ vi_fragments);

										(*ampdu_len) += vi_fragments;
										RAStas[rit->second].send_media_mu="V";
										RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, vi_fragments, FRAGMENT_SIZE, 0, PACKET_SIZE_BWD_HA, bw);

										++(*accesstemp_mu);
										++(*accesstemp);

										// remove retry details of sent packets
										for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
											if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
												++count_remove_sent_ul;
											}
										}

										(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
												count_remove_sent_ul);
										(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
												count_remove_sent_ul);


										vi_ofdma_count += vi_fragments;
										total_vid_fragments += vi_fragments;
										count_remove_sent_ul=0;
									}


//									transmitting all HA samples due to multi-TID feature
									if (ha_frames>0){
										RAStas[rit->second].ampduLength_ha.push_back(ha_frames);
										RAStas[rit->second].interAccess_ha.push_back(sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_ha);

										sta_interAccess_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
										if (!RAStas[rit->second].vid_last)
											sta_interAccess_mu_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
										else
											sta_interAccess_mu_ha_vid.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

										RAStas[rit->second].lastAccess_ha = sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);
										RAStas[rit->second].lastAccess_pois_ha = sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);

										if (vi_fragments>0)
											RAStas[rit->second].vid_last=true;

										vid_delay_file << "Number of haptic frames: " << ha_frames << endl;
										RAStas[rit->second].edca_ampdu_len = ha_frames;
										RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
										RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
										RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];

										total_hap_frames += ha_frames;
										// record the delays
										RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-optimal_dur_ul+RAStas[rit->second].haptic_dur_ul_delay-RAStas[rit->second].queueheadTime;
										RAStas[rit->second].hap_frames_sent += RAStas[rit->second].edca_ampdu_len;

										vid_delay_file << "----- MultiTID----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
												sim_time << "\tQ-size: " << ha_frames << "\tSampleDelays: " ;

										if(RAStas[rit->second].send_media_mu.compare("V")==0){
											vid_delay_file << "\nLogging Video+Haptic\n" << endl;
											RAStas[rit->second].send_media_mu="HV";
										}
										else{
											RAStas[rit->second].send_media_mu="H";
											vid_delay_file << "\nLogging Haptic\n" << endl;
										}

										for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
											// w/o accounting for jitter buffer delay
											RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
											vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";

											// accounting for jitter buffer delay
											RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));

										}
										vid_delay_file << endl;

										// clear data queue
										pacQ_STA_ha[rit->second].clear();

										vid_delay_file << "Q of STA " << rit->second << " cleared." << endl;
										// clear retry queue
										retry_cnt_STA_ha[rit->second].clear();
										retxQ_STA_ha[rit->second].clear();
										RAStas[rit->second].bt_ha=-1;
										RAStas[rit->second].cw_ha=0;

										vid_delay_file << "multi-TID done" << endl;
										txed_vi_fragments=vi_fragments;
										txed_ha_frames=ha_frames;
										RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, txed_vi_fragments, FRAGMENT_SIZE, txed_ha_frames, PACKET_SIZE_BWD_HA, bw);


									}

									--nULSTAs;
									if (nULSTAs==0){
										ul_sampleCount.clear();
										break;
									}

								}

//								NO VI data; hence only HA to be sent
								else if (!ha_empty && vi_empty){
									RAStas[rit->second].send_media_mu="H";

									RAStas[rit->second].ampduLength_ha.push_back(ha_frames);
									RAStas[rit->second].interAccess_ha.push_back(sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_ha);

									sta_interAccess_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
									if (!RAStas[rit->second].vid_last)
										sta_interAccess_mu_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
										duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

									else
										sta_interAccess_mu_ha_vid.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
										duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

									RAStas[rit->second].lastAccess_ha = sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);
									RAStas[rit->second].lastAccess_pois_ha = sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);

									RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-optimal_dur_ul+RAStas[rit->second].haptic_dur_ul_delay-(*pacQ_holder)[rit->second].front();
									vid_delay_file << "inside HA again" << endl;
									RAStas[rit->second].vid_last=false;

									// record the delays
									RAStas[rit->second].edca_ampdu_len = ha_frames;
									RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
									RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
									RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];

									//									RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-RAStas[rit->second].queueheadTime;

									vid_delay_file << "----- Direct haptic in UL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
											sim_time << "\tSampleDelays: " ;

									for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
										// w/o accounting for jitter buffer delay
										if ((RAStas[rit->second].delay-z*HA_DURATION)<300000){
										RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
										vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
										}
										// accounting for jitter buffer delay
										RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));

									}

									total_hap_frames += ha_frames;
									vid_delay_file << endl;
									RAStas[rit->second].bt_ha=-1;
									RAStas[rit->second].cw_ha=0;

									// clear data queue
									pacQ_STA_ha[rit->second].clear();
									// clear retry queue
									retry_cnt_STA_ha[rit->second].clear();
									retxQ_STA_ha[rit->second].clear();

									txed_vi_fragments=0;
									txed_ha_frames=ha_frames;
									RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, txed_vi_fragments, FRAGMENT_SIZE, txed_ha_frames, PACKET_SIZE_BWD_HA, bw);
									--nULSTAs;
									if (nULSTAs==0){
										ul_sampleCount.clear();
										break;
									}
								}
							}

//							if there is no space for (i) even 1 VI frame OR (ii) 1 VI frame and all HA frames OR (iii) all HA frames
							else{
								if (!vi_empty){
									if (!pacQ_STA_vi[rit->second].empty()){
										--vi_stas;
									}
									else if (!pacQ_STA_ha[rit->second].empty()){
										--ha_only_stas;
										vid_delay_file << "Only HA frames here as no VI frames queued up" << endl;
									}

//									removing 1 VI frame makes space for some HA frames
									if(getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){

										RAStas[rit->second].ampduLength_ha.push_back(ha_frames);
										RAStas[rit->second].interAccess_ha.push_back(sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_ha);

										sta_interAccess_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

										if (!RAStas[rit->second].vid_last)
											sta_interAccess_mu_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
										else
											sta_interAccess_mu_ha_vid.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);


										RAStas[rit->second].lastAccess_ha = sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);
										RAStas[rit->second].lastAccess_pois_ha = sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);

										RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-optimal_dur_ul+RAStas[rit->second].haptic_dur_ul_delay-(*pacQ_holder)[rit->second].front();
										vid_delay_file << "Can send 0 VI frames and all HA frames" << endl;
										RAStas[rit->second].send_media_mu="H";
										RAStas[rit->second].vid_last=false;

										// record the delays
										RAStas[rit->second].edca_ampdu_len = ha_frames;
										RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
										RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
										RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];

										//									RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-RAStas[rit->second].queueheadTime;

										vid_delay_file << "----- Direct haptic in UL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
												sim_time << "\tSampleDelays: " ;

										for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
											// w/o accounting for jitter buffer delay
											if ((RAStas[rit->second].delay-z*HA_DURATION)<300000){
											RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
											vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
											}
											// accounting for jitter buffer delay
											RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));

										}
										vid_delay_file << endl;
										RAStas[rit->second].bt_ha=-1;
										RAStas[rit->second].cw_ha=0;

										total_hap_frames += ha_frames;

										// clear data queue
										pacQ_STA_ha[rit->second].clear();
										// clear retry queue
										retry_cnt_STA_ha[rit->second].clear();
										retxQ_STA_ha[rit->second].clear();

										txed_vi_fragments=0;
										txed_ha_frames=ha_frames;
										RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, txed_vi_fragments, FRAGMENT_SIZE, txed_ha_frames, PACKET_SIZE_BWD_HA, bw);
										--nULSTAs;
										if (nULSTAs==0){
											ul_sampleCount.clear();
											break;
										}
									}
//									after removing VI frame, checking if removing some HA frames helps
									else{
										ha_frames=0;
										while(getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, ++ha_frames, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){
											continue;
										}
//										some HA frames can be sent
										if (--ha_frames >0){

											RAStas[rit->second].interAccess_ha.push_back(sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_ha);

											sta_interAccess_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

											if(!RAStas[rit->second].vid_last)
												sta_interAccess_mu_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
											else
												sta_interAccess_mu_ha_vid.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);


											RAStas[rit->second].lastAccess_ha = sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);
											RAStas[rit->second].lastAccess_pois_ha = sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
													duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);

											vid_delay_file << "Can send only " << ha_frames << " HA frames" << endl;
											RAStas[rit->second].send_media_mu="H";
											// compute the extra samples
											extra = pacQ_STA_ha[rit->second].size()-ha_frames;
											vid_delay_file << "------ < optimal ------" << endl;
											vid_delay_file << "QueuedFrames: " << pacQ_STA_ha[rit->second].size() << "\tSendableFrames: " << ha_frames
													<< "\tExtraSamples: " << extra << endl;
											pacQ_STA_ha[rit->second].erase(pacQ_STA_ha[rit->second].begin(), pacQ_STA_ha[rit->second].begin()+extra);


											RAStas[rit->second].edca_ampdu_len = pacQ_STA_ha[rit->second].size();
											RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
											RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
											RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];
											RAStas[rit->second].dropped_ha += extra;
											RAStas[rit->second].hap_frames_sent += RAStas[rit->second].edca_ampdu_len;
											RAStas[rit->second].ampduLength_ha.push_back(RAStas[rit->second].edca_ampdu_len);

											RAStas[rit->second].vid_last=false;

											// record the delays
											RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-optimal_dur_ul+RAStas[rit->second].haptic_dur_ul_delay-RAStas[rit->second].queueheadTime;

											vid_delay_file << "----- Direct haptic in UL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
													sim_time << "\tSampleDelays: " ;

											for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
												// w/o accounting for jitter buffer delay
												if ((RAStas[rit->second].delay-z*HA_DURATION)<300000){
												RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
												vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
												}
												// accounting for jitter buffer delay
												RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));

											}
											vid_delay_file << endl;
											total_hap_frames += RAStas[rit->second].edca_ampdu_len;

											txed_vi_fragments=0;
											txed_ha_frames=ha_frames;
											RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, txed_vi_fragments, FRAGMENT_SIZE, txed_ha_frames, PACKET_SIZE_BWD_HA, bw);

											// clear data queue
											pacQ_STA_ha[rit->second].clear();
											vid_delay_file << "Q of STA " << rit->second << " cleared." << endl;
											// clear retry queue
											retry_cnt_STA_ha[rit->second].clear();
											retxQ_STA_ha[rit->second].clear();
											RAStas[rit->second].bt_ha=-1;
											RAStas[rit->second].cw_ha=0;
											//											RAStas[rit->second].cw_ha = CW_MIN_HA;

											vid_delay_file << "multi-TID done" << endl;
										}
//										not even 1 HA frame can be sent
										else{
											vid_delay_file << "Cannot send anything" << endl;
										}
									}
								}
								else if (!ha_empty && vi_empty){
									ha_frames=0;
									while(getOfdmaAMpduDuration (mcs, tone_ul, 0, FRAGMENT_SIZE, ++ha_frames, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){
										continue;
									}
									//										some HA frames can be sent
									if (--ha_frames >0){

										RAStas[rit->second].interAccess_ha.push_back(sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_ha);
										sta_interAccess_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

										if(!RAStas[rit->second].vid_last)
											sta_interAccess_mu_ha.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);
										else
											sta_interAccess_mu_ha_vid.push_back(sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
											duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back)-RAStas[rit->second].lastAccess_pois_ha);

										RAStas[rit->second].lastAccess_ha = sim_time-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);
										RAStas[rit->second].lastAccess_pois_ha = sim_time+RAStas[rit->second].haptic_dur_ul-((total_length_ul>STA_RTS_THRESHOLD)*(RTS_TIME + CTS_TIME) +
												duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back);

										vid_delay_file << "Can send only " << ha_frames << " HA frames" << endl;
										RAStas[rit->second].send_media_mu="H";
										// compute the extra samples
										extra = pacQ_STA_ha[rit->second].size()-ha_frames;
										vid_delay_file << "------ < optimal ------" << endl;
										vid_delay_file << "QueuedFrames: " << pacQ_STA_ha[rit->second].size() << "\tSendableFrames: " << ha_frames
												<< "\tExtraSamples: " << extra << endl;
										pacQ_STA_ha[rit->second].erase(pacQ_STA_ha[rit->second].begin(), pacQ_STA_ha[rit->second].begin()+extra);

										RAStas[rit->second].edca_ampdu_len = pacQ_STA_ha[rit->second].size();
										RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
										RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
										RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];
										RAStas[rit->second].dropped_ha += extra;
										RAStas[rit->second].hap_frames_sent += RAStas[rit->second].edca_ampdu_len;
										RAStas[rit->second].ampduLength_ha.push_back(RAStas[rit->second].edca_ampdu_len);
										RAStas[rit->second].vid_last=false;

										// record the delays
										RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-optimal_dur_ul+RAStas[rit->second].haptic_dur_ul_delay-RAStas[rit->second].queueheadTime;

										vid_delay_file << "----- Direct haptic in UL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
												sim_time << "\tSampleDelays: " ;

										for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
											// w/o accounting for jitter buffer delay
											if ((RAStas[rit->second].delay-z*HA_DURATION)<300000){
												RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
												vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
											}

											// accounting for jitter buffer delay
											RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));

										}
										vid_delay_file << endl;
										total_hap_frames += RAStas[rit->second].edca_ampdu_len;

										// clear data queue
										pacQ_STA_ha[rit->second].clear();
										vid_delay_file << "Q of STA " << rit->second << " cleared." << endl;
										// clear retry queue
										retry_cnt_STA_ha[rit->second].clear();
										retxQ_STA_ha[rit->second].clear();
										RAStas[rit->second].bt_ha=-1;
										RAStas[rit->second].cw_ha=0;
										//											RAStas[rit->second].cw_ha = CW_MIN_HA;

										txed_vi_fragments=0;
										txed_ha_frames=ha_frames;
										RAStas[rit->second].ul_duration=getOfdmaAMpduDuration (mcs, tone_ul, txed_vi_fragments, FRAGMENT_SIZE, txed_ha_frames, PACKET_SIZE_BWD_HA, bw);

										vid_delay_file << "multi-TID done" << endl;
									}
//																			not even 1 HA frame can be sent
									else{
										vid_delay_file << "Cannot send anything" << endl;
									}
								}
							}


//							if (getOfdmaAMpduDuration (mcs, tone_ul, vi_fragments, FRAGMENT_SIZE, ha_frames, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){
//
////							if (rit->first <= optimal_len_ul){
////								printf("\n AMPDU: %d \t max duration: %d\n", rit->first, optimal_dur_ul);
//								if (rit->second == 0){
//									ul_zero_ofdma_ampdu += rit->first;
//									++ul_zero_ofdma_access;
//								}
//
//
//								ul_ofdma_tot_frame += rit->first;
////								cout << "\nTotal UL frames ---- Prev: " << ul_ofdma_tot_frame-rit->first << "\t Now: " << ul_ofdma_tot_frame << endl;
//								RAStas[rit->second].nTx += rit->first;
//
//								RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front();
////								printf("\n AMPDU: %d \t max duration: %d\n", rit->first, optimal_dur_ul);
//
//								(*lastSent_temp)=(*pacQ_holder)[rit->second].back(); //+(rit->first-1)*duration;
////								vid_delay_file << "STA: " << rit->second << "  Prev. spill over: " << RAStas[rit->second].fragments_sent << "\t";
//
////								vid_delay_file << "Prev. spill over + sent: " << RAStas[rit->second].fragments_sent << endl;
////								RAStas[rit->second].vid_frames_sent += rit->first;
//
////								only in case of video chosen in UL-OFDMA
////								if((ha_ulofdma%p==0)) { // ha_ulofdma%3==0
//								if(!vi_empty){
//									vid_delay_file << "inside VI" << endl;
//									RAStas[rit->second].fragments_sent += rit->first;
//									// recording video delays
//									if (RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
//										num_frames_sent=0;
//										//									vid_delay_file << "#FragmentsSent: " << RAStas[rit->second].fragments_sent << "\tQ-sizeFront: " << (*pacQ_size_holder)[rit->second].front() << endl;
//										while(RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
//											vid_delay_file << endl ;
//											++RAStas[rit->second].frames_sent;
//											++RAStas[rit->second].vid_frames_sent;
//											++num_frames_sent;
//											// record video delays
//											// w/o accounting for jitter buffer
//											RAStas[rit->second].sampleAccessDelayVid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION)));
//
//											// accounting for jitter buffer
//											(*delaystemp).push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))+(num_frames_sent-1)*VI_DURATION);
//											//										delay_vid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))/1000.0);
//											vid_delay_file << "STA: " << rit->second << "\t" << RAStas[rit->second].frames_sent-1 << "\t" <<
//													(RAStas[rit->second].frames_sent-1)*VI_DURATION/1000.0 << "\t" << sim_time << "\t" << (*delaystemp).back() << "\tQueued: " << rit->first
//													<<  "\t#sent: " << RAStas[rit->second].fragments_sent ;
//
//											RAStas[rit->second].fragments_sent = RAStas[rit->second].fragments_sent-(*pacQ_size_holder)[rit->second].front();
//											(*pacQ_size_holder)[rit->second].erase((*pacQ_size_holder)[rit->second].begin(), (*pacQ_size_holder)[rit->second].begin()+1);
//
//										}
//
//										vid_delay_file << "\tspill-over: " << RAStas[rit->second].fragments_sent <<  "\tUL-OFDMA: " << rit->first << "\topt: " << optimal_len_ul
//												<< "\tUL-OFDMA<opt" << endl;
//
//
//									}
//
//									else{
//										vid_delay_file << "-----------INCOMPLETE FRAME TRANSMISSION----------" << endl;
//										vid_delay_file <<  "STA: " << rit->second << "\tspill-over" << RAStas[rit->second].fragments_sent << "\tFrameSize: " << (*pacQ_size_holder)[rit->second].front()
//													<< "\tUL-OFDMA<opt" << endl;
//									}
//
////									// recording delays
////									for (int z=0;z<rit->first;z++){ //
////										// w/o accounting for jitter buffer delay
////										//									(*delaystemp).push_back((RAStas[rit->second].delay-z*duration));
////										//  accounting for jitter buffer delay
////										if ()
////											(*delaystemp).push_back((RAStas[rit->second].delay));
////										(*delays_mu).push_back((RAStas[rit->second].delay-z*duration));
////										//									printf("STA %d \t Media: %s \t sim_time: %d \t Sample: %d \t AMPDU: %d \t duration: %d \t max_duration: %d \t delay: %d\n",
////										// 											rit->second, media.c_str(), sim_time, (*pacQ_holder)[rit->second].front()+z*duration, rit->first,
////										//											optimal_dur_ul, optimal_dur_ul, (*delaystemp).back());
////
////
////										if (rit->second==0){
////											output_file_STA << (*pacQ_holder)[rit->second].front()*1.0/duration+z << "\t" <<
////													(*pacQ_holder)[rit->second].front()*1.0/duration+z+(*delaystemp).back()/1000.0 << "\tUL-SA\n";
////											ul_zero_ofdma_delay.push_back((*delaystemp).back());
////										}
////
////										//output_file_STA << "STA" << i << "    sim_time:" << sim_time << "    AMPDU:" << RAStas[i].edca_ampdu_len << "    queuehead:" <<
////										//			RAStas[i].queueheadTime/1000 << "    delay:" << RAStas[i].delay-z*1000 << "\n";
////									}
////
////									----------------------------------------------------
////									if ((rit->second==0) && (media.compare("VI")==0)){
////										staO_file << "sim_time: " << sim_time << " --- transmitting frames from " << (*pacQ_holder)[rit->second].front() << " upto " <<
////												(*pacQ_holder)[rit->second].front()+(rit->first-1)*duration << endl;
////										cout << "sim_time: " << sim_time << " --- transmitting frames from " << (*pacQ_holder)[rit->second].front() << " upto " <<
////												(*pacQ_holder)[rit->second].front()+(rit->first-1)*duration << endl;
////									}
////									----------------------------------------------------
//
//									(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+
//											rit->first);
//
//									(*ampdu_len) += rit->first;
//									//ampdu_len_mu += rit->first;
//									++(*accesstemp_mu);
//									++(*accesstemp);
//
//									// reset the BT here if UL-OFDMA is achieved
////									if (nSenders_ha==1){
////										RAStas[rit->second].bt_ha=-1;
////									}
////									else{
////										RAStas[rit->second].bt_vi=-1;
////									}
//
//									// remove retry details of sent packets
//									for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
//										if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
//											++count_remove_sent_ul;
//										}
//									}
//
//									(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
//											count_remove_sent_ul);
//									(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
//											count_remove_sent_ul);
//
//									--nULSTAs;
//									vi_ofdma_count += rit->first;
//									count_remove_sent_ul=0;
//
//
//
//////									STA with highest video data; find total feasible size including haptic and video
////									if (rit->second == highest_sta_ul){
////										if (optimal_queue_ul*FRAGMENT_SIZE+pacQ_STA_ha[highest_sta_ul].size()*PACKET_SIZE_BWD_HA <= max_len_ul*FRAGMENT_SIZE){
////											max_len_ul_batch = optimal_queue_ul*FRAGMENT_SIZE+pacQ_STA_ha[highest_sta_ul].size()*PACKET_SIZE_BWD_HA;
//////											hap_size_highest_sta = pacQ_STA_ha[highest_sta_ul].size();
////										}
////										else{
//////											hap_size_highest_sta = floor((max_len_ul*FRAGMENT_SIZE-optimal_queue_ul*FRAGMENT_SIZE)*1.0/PACKET_SIZE_BWD_HA);
////											max_len_ul_batch = max_len_ul*FRAGMENT_SIZE;
////										}
////										extra_dur_ul = getOfdmaAMpduDuration (mcs, tone_ul, optimal_len_ul, packet_size, bw);
////									}
//
////									if (optimal_queue_ul*FRAGMENT_SIZE+pacQ_STA_ha[highest_sta_ul].size()*PACKET_SIZE_BWD_HA < max_len_ul*FRAGMENT_SIZE){
////										max_len_ul_batch = optimal_queue_ul*FRAGMENT_SIZE+pacQ_STA_ha[highest_sta_ul].size()*PACKET_SIZE_BWD_HA;
////										max_hap_size = max_len_ul_batch-pacQ_STA_ha[highest_sta_ul].size()
////									}
////									else{
////										max_len_ul_batch = max_len_ul*FRAGMENT_SIZE;
////									}
//
//
////									transmitting haptic samples due to multi-TID feature with potential frame drops
//									if (pacQ_STA_ha[rit->second].size()>0){
//
//										if (getOfdmaAMpduDuration (mcs, tone_ul, rit->first, FRAGMENT_SIZE, 0, 0, bw)<optimal_dur_ul){
//											hap_len_sta = pacQ_STA_ha[rit->second].size();
//											vid_delay_file << "Number of haptic frames: " << hap_len_sta << endl;
//											// all haptic samples can be sent in the remaining slot
//											if (getOfdmaAMpduDuration (mcs, tone_ul, rit->first, FRAGMENT_SIZE, hap_len_sta, PACKET_SIZE_BWD_HA, bw)<=optimal_dur_ul){
//
//												RAStas[rit->second].edca_ampdu_len = hap_len_sta;
//												RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
//												RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
//												RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];
//
//												// record the delays
//												RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-RAStas[rit->second].queueheadTime;
//												RAStas[rit->second].hap_frames_sent += RAStas[rit->second].edca_ampdu_len;
//
//												vid_delay_file << "----- MultiTID----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
//														sim_time << "\tQ-size: " << hap_len_sta << "\tSampleDelays: " ;
//
//												for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
//													// w/o accounting for jitter buffer delay
//													RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
//													vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
//
//													// accounting for jitter buffer delay
//													RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));
//
//												}
//												vid_delay_file << endl;
//
//												// clear data queue
//												pacQ_STA_ha[rit->second].clear();
//												vid_delay_file << "Q of STA " << rit->second << " cleared." << endl;
//												// clear retry queue
//												retry_cnt_STA_ha[rit->second].clear();
//												retxQ_STA_ha[rit->second].clear();
//												RAStas[rit->second].bt_ha=-1;
//												//											RAStas[rit->second].cw_ha = CW_MIN_HA;
//
//
//												RAStas[rit->second].accessTimeVec_ha.push_back(sim_time-RAStas[rit->second].accessTime_ha);
//												RAStas[rit->second].accessTime_ha=sim_time;
//												vid_delay_file << "multi-TID done" << endl;
//											}
//
//											// only some haptic samples can be sent in the remaining slot
//											// in this case, send only the latest feasible samples dropping the rest
//											else{
//												// compute the extra samples
//												while(getOfdmaAMpduDuration (mcs, tone_ul, rit->first, FRAGMENT_SIZE, --hap_len_sta, PACKET_SIZE_BWD_HA, bw)>optimal_dur_ul){
//													continue;
//												}
//												extra = pacQ_STA_ha[rit->second].size()-hap_len_sta;
//												vid_delay_file << "------ < optimal ------" << endl;
//												vid_delay_file << "QueuedFrames: " << pacQ_STA_ha[rit->second].size() << "\tSendableFrames: " << hap_len_sta
//														<< "\tExtraSamples: " << extra << endl;
//												//										for(int a=0;a<extra;a++){
//												pacQ_STA_ha[rit->second].erase(pacQ_STA_ha[rit->second].begin(), pacQ_STA_ha[rit->second].begin()+extra);
//												//										}
//
//
//												RAStas[rit->second].edca_ampdu_len = pacQ_STA_ha[rit->second].size();
//												RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
//												RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
//												RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];
//												RAStas[rit->second].dropped_ha += extra;
//												RAStas[rit->second].hap_frames_sent += RAStas[rit->second].edca_ampdu_len;
//
//
//												// record the delays
//												RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-RAStas[rit->second].queueheadTime;
//
//												vid_delay_file << "----- MultiTID----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
//														sim_time << "\tSampleDelays: " ;
//
//												for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
//													// w/o accounting for jitter buffer delay
//													RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
//													vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
//
//													// accounting for jitter buffer delay
//													RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));
//
//												}
//												vid_delay_file << endl;
//
//												// clear data queue
//												pacQ_STA_ha[rit->second].clear();
//												vid_delay_file << "Q of STA " << rit->second << " cleared." << endl;
//												// clear retry queue
//												retry_cnt_STA_ha[rit->second].clear();
//												retxQ_STA_ha[rit->second].clear();
//												RAStas[rit->second].bt_ha=-1;
//												//											RAStas[rit->second].cw_ha = CW_MIN_HA;
//
//												RAStas[rit->second].accessTimeVec_ha.push_back(sim_time-RAStas[rit->second].accessTime_ha);
//												RAStas[rit->second].accessTime_ha=sim_time;
//												vid_delay_file << "multi-TID done" << endl;
//
//											}
//										}
//									}
//
//
//									if (nULSTAs==0){
//										break;
//									}
//								}
//
////								only in case of haptic chosen in UL-OFDMA
//								else if (!ha_empty){
//									vid_delay_file << "inside HA again" << endl;
//									// record the delays
//									RAStas[rit->second].edca_ampdu_len = pacQ_STA_ha[rit->second].size();
//									RAStas[rit->second].nTx += RAStas[rit->second].edca_ampdu_len;
//									RAStas[rit->second].queueheadTime = pacQ_STA_ha[rit->second].front();
//									RAStas[rit->second].lastSent_ha = pacQ_STA_ha[rit->second][RAStas[rit->second].edca_ampdu_len-1];
//
////									RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-RAStas[rit->second].queueheadTime;
//
//									vid_delay_file << "----- Direct haptic in UL-OFDMA ----- \nSTA: " << rit->second << "\tQ-head: " << RAStas[rit->second].queueheadTime << "\ttime: " <<
//											sim_time << "\tSampleDelays: " ;
//
//									for (int z=0;z<RAStas[rit->second].edca_ampdu_len;z++){ //
//										// w/o accounting for jitter buffer delay
//										RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*HA_DURATION));
//										vid_delay_file << RAStas[rit->second].sampleAccessDelay.back() << "   ";
//
//										// accounting for jitter buffer delay
//										RAStas[rit->second].delaysList.HA.push_back((RAStas[rit->second].delay));
//
//									}
//									vid_delay_file << endl;
//									RAStas[rit->second].bt_ha=-1;
////									RAStas[rit->second].cw_ha = CW_MIN_HA;
//
//									// clear data queue
//									pacQ_STA_ha[rit->second].clear();
//									// clear retry queue
//									retry_cnt_STA_ha[rit->second].clear();
//									retxQ_STA_ha[rit->second].clear();
//
//									--nULSTAs;
//									if (nULSTAs==0){
//										break;
//									}
//								}
//							}
//
//							else{
//
//								if (!ha_empty && vi_empty){
//									vid_delay_file << "Q-size: " << rit->first << "\tfeasible: " << optimal_len_ul << endl;
////									break;
//									RAStas[rit->second].nTx += optimal_len_ul;
//									RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front();
//
//									(*lastSent_temp)=(*pacQ_holder)[rit->second].front()+(optimal_len_ul-1)*duration;
//
//									// recording haptic delays
//									for (int z=0;z<optimal_len_ul;z++){ //
//										// w/o accounting for jitter buffer delay
//										RAStas[rit->second].sampleAccessDelay.push_back((RAStas[rit->second].delay-z*duration));
//
//										// accounting for jitter buffer delay
//										RAStas[rit->second].delaysList.HA.push_back(RAStas[rit->second].delay);
//
//									}
//
//
//									(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+optimal_len_ul);
//									//								cout << "\nQueue length: \t" << (*pacQ_holder)[rit->second].size() << endl;
//									//								cout << (*pacQ_holder)[rit->second].front() << endl;
//
//									RAStas[rit->second].queueheadTime = (*pacQ_holder)[rit->second].front();
//									(*ampdu_len) += optimal_len_ul;
//									//ampdu_len_mu += optimal_len_ul;
//									++(*accesstemp_mu);
//									++(*accesstemp);
//
//									// remove retry details of sent packets
//									for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
//										if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
//											++count_remove_sent_ul;
//										}
//									}
//
//									(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
//											count_remove_sent_ul);
//									(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
//											count_remove_sent_ul);
//									--nULSTAs;
//									count_remove_sent_ul=0;
//									if (nULSTAs==0){
//										break;
//									}
//									continue;
//								}
//
//								if (rit->second == 0){
//									ul_zero_ofdma_ampdu += optimal_len_ul;
//									++ul_zero_ofdma_access;
//								}
//
//								ul_ofdma_tot_frame += optimal_len_ul;
//								//cout << "\nTotal DL frames ---- Prev: " << ul_ofdma_tot_frame-optimal_len_ul << "\t Now: " << ul_ofdma_tot_frame << endl;
//
////								************** CONTINUE FROM HERE ***************
////								************** WHEN NOT ALL VI FRAMES CAN BE SENT ***************
//								RAStas[rit->second].nTx += optimal_len_ul;
//								RAStas[rit->second].delay = sim_time-SIFS-duration_multi_sta_back-(*pacQ_holder)[rit->second].front();
//
////								printf("\n AMPDU: %d \t max length: %d \t max duration: %d\n", rit->first, optimal_len_ul, optimal_dur_ul);
//
//								(*lastSent_temp)=(*pacQ_holder)[rit->second].front()+(optimal_len_ul-1)*duration;
//
////								vid_delay_file << "STA: " << rit->second << "  Prev. spill over: " << RAStas[rit->second].fragments_sent << "\t";
//								RAStas[rit->second].fragments_sent += optimal_len_ul;
////								vid_delay_file << "Prev. spill over + sent: " << RAStas[rit->second].fragments_sent << endl;
//
//
//								if (RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
//									num_frames_sent=0;
////									vid_delay_file << "#FragmentsSent: " << RAStas[rit->second].fragments_sent << "\tQ-sizeFront: " << (*pacQ_size_holder)[rit->second].front() << endl;
//									while(RAStas[rit->second].fragments_sent>=(*pacQ_size_holder)[rit->second].front()){
//										++RAStas[rit->second].frames_sent;
//										++RAStas[rit->second].vid_frames_sent;
//										++num_frames_sent;
//										// record video delays
//										// w/o accounting for jitter buffer
//										RAStas[rit->second].sampleAccessDelayVid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION)));
//
//										// accounting for jitter buffer
//										(*delaystemp).push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))+(num_frames_sent-1)*VI_DURATION);
//
//										vid_delay_file << "STA: " << rit->second << "\t" << RAStas[rit->second].frames_sent-1 << "\t" <<
//												(RAStas[rit->second].frames_sent-1)*VI_DURATION/1000.0 << "\t" << sim_time << "\t" << (*delaystemp).back() << "\tQueued: " << rit->first
//												<< "\tSent: " << RAStas[rit->second].fragments_sent  << endl;
//
//										RAStas[rit->second].fragments_sent = RAStas[rit->second].fragments_sent-(*pacQ_size_holder)[rit->second].front();
//										(*pacQ_size_holder)[rit->second].erase((*pacQ_size_holder)[rit->second].begin(), (*pacQ_size_holder)[rit->second].begin()+1);
//
//									}
//
//
//									vid_delay_file << "\tspill-over: " << RAStas[rit->second].fragments_sent << "\tUL-OFDMA: " << rit->first << "\topt: " << optimal_len_ul
//											<< "\tUL-OFDMA>opt" << endl;
//
//
//								}
//
//								else{
//									vid_delay_file << "----------- INCOMPLETE FRAME TRANSMISSION ----------" << endl;
//									vid_delay_file <<  "STA: " << rit->second << "\tspill-over: " << RAStas[rit->second].fragments_sent << "\tFrameSize: " << (*pacQ_size_holder)[rit->second].front()
//													<< "\tUL-OFDMA>opt" << endl;
//								}
//
//
////								// recording video delays
////								if (RAStas[rit->second].fragments_sent>=no_fragments){
////									tempframes = RAStas[rit->second].fragments_sent/no_fragments;
////
////									for (int b=0; b<tempframes; b++){
////										++RAStas[rit->second].frames_sent;
////
////										// w/o accounting for jitter buffer
////										RAStas[rit->second].sampleAccessDelayVid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION)));
////
////										// accounting for jitter buffer
////										(*delaystemp).push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))+b*VI_DURATION);
////
//////										(*delaystemp).push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION)));
//////										delay_vid.push_back((sim_time-SIFS-duration_multi_sta_back-((RAStas[rit->second].frames_sent-1)*VI_DURATION))/1000.0);
////										vid_delay_file << "STA: " << rit->second << "\t" << RAStas[rit->second].frames_sent-1 << "\t" <<
////												(RAStas[rit->second].frames_sent-1)*VI_DURATION/1000.0 << "\t" << sim_time << "\t" << (*delaystemp).back() << "\tQueued: " << rit->first
////												<< "\tSent: " << RAStas[rit->second].fragments_sent ;
////										if (b==tempframes-1){
////											RAStas[rit->second].fragments_sent = (RAStas[rit->second].fragments_sent)-tempframes*no_fragments;
////											vid_delay_file << "\tspill-over: " << RAStas[rit->second].fragments_sent << "\tUL-OFDMA: " << rit->first << "\topt: " << optimal_len_ul
////											<< "\tUL-OFDMA>opt" << endl;
////											break;
////										}
////										vid_delay_file << endl;
////									}
////
////								}
//
//								// recording delays
////								for (int z=0;z<optimal_len_ul;z++){ //
////									// w/o accounting for jitter buffer delay
//////									(*delaystemp).push_back((RAStas[rit->second].delay-z*duration));
////
////									// accounting for jitter buffer delay
////									(*delaystemp).push_back((RAStas[rit->second].delay));
////									(*delays_mu).push_back((RAStas[rit->second].delay-z*duration));
//////									printf("STA %d \t Media: %s \t sim_time: %d \t Sample: %d \t AMPDU: %d \t duration: %d \t max_duration: %d \t delay: %d\n",
//////											rit->second, media.c_str(), sim_time, (*pacQ_holder)[rit->second].front()+z*duration, rit->first,
//////											optimal_dur_ul, optimal_dur_ul, (*delaystemp).back());
////									if (rit->second==0){
////										output_file_STA << (*pacQ_holder)[rit->second].front()*1.0/duration+z << "\t" <<
////												(*pacQ_holder)[rit->second].front()*1.0/duration+z+(*delaystemp).back()/1000.0 << "\tUL-SA\n";
////										ul_zero_ofdma_delay.push_back((*delaystemp).back());
////									}
////								}
//
////								cout << "\nPackets before & removal: \t" << pacQ_STA_ha[rit->second].front() << " --> ";
//
//								// ----------------------------------------------------
//								if ((rit->second==0) && (media.compare("VI")==0)){
//									staO_file << "\ntime: " <<  sim_time << "    Transmitting from " << (*pacQ_holder)[rit->second].front() << "  to  "<<
//											(*pacQ_holder)[rit->second].front()+(optimal_len_ul-1)*duration <<  " & hence flushing " <<
//											count_remove_sent_ul << " entries from RTRQ" << endl;
////									cout << "\ntime: " <<  sim_time << "    Transmitting from " << (*pacQ_holder)[rit->second].front() << "  to  "<<
////																				(*pacQ_holder)[rit->second].front()+(optimal_len_ul-1)*duration <<  " & hence flushing " <<
////																				count_remove_sent_ul << " entries from RTRQ" << endl;
//								}
//								// ----------------------------------------------------
//
//								(*pacQ_holder)[rit->second].erase((*pacQ_holder)[rit->second].begin(), (*pacQ_holder)[rit->second].begin()+optimal_len_ul);
////								cout << "\nQueue length: \t" << (*pacQ_holder)[rit->second].size() << endl;
////								cout << (*pacQ_holder)[rit->second].front() << endl;
//
//								RAStas[rit->second].queueheadTime = (*pacQ_holder)[rit->second].front();
//								(*ampdu_len) += optimal_len_ul;
//								//ampdu_len_mu += optimal_len_ul;
//								++(*accesstemp_mu);
//								++(*accesstemp);
//
//								// remove retry details of sent packets
//								for (int m=0;m<(*retxQ_holder)[rit->second].size();m++){
//									if ((*lastSent_temp)>=(*retxQ_holder)[rit->second][m]){
//										++count_remove_sent_ul;
//									}
//								}
//
//								(*retxQ_holder)[rit->second].erase((*retxQ_holder)[rit->second].begin(), (*retxQ_holder)[rit->second].begin()+
//										count_remove_sent_ul);
//								(*retry_cnt_holder)[rit->second].erase((*retry_cnt_holder)[rit->second].begin(), (*retry_cnt_holder)[rit->second].begin()+
//										count_remove_sent_ul);
//								--nULSTAs;
//								count_remove_sent_ul=0;
//								vi_ofdma_count += optimal_len_ul;
//								if (nULSTAs==0){
//									break;
//								}
//							}

							vid_delay_file << "Effectively sent: " << txed_vi_fragments << " VI frames & " << txed_ha_frames << " HA frames" << endl;
						}

						// remove sent STAs and go back to DL_OFDMA after first batch if sim_time left
						for (auto it=ul_sampleCount.begin(); it!=ul_sampleCount.end(); ++it){
							if (it->second == stas_ul.back()){
								ul_sampleCount.erase(it, ul_sampleCount.end());
								break;
							}
						}
//						for (auto it=ul_sampleCount.begin(); it!=ul_sampleCount.end(); ++it){
//							std::vector<int>::iterator temp;
//							temp = find (stas_ul.begin(), stas_ul.end(), it->second);
//							if (temp!=stas_ul.end()){
//								ul_sampleCount.erase(it);
//							}
//						}
						stas_ul.clear();
//						break;
						vid_delay_file << "Time left: " << timeleft << endl;
					}

//				vid_delay_file << "Here I am" << endl;
				if (inside_ulofdma){
					for(int l=0; l<nRAStas; l++){
						if (RAStas[l].ul_duration>0){
							if (RAStas[l].send_media_mu.compare("HV")==0){

								logging_file << sim_time-( bsrptime + SIFS + bsrtime + duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";" <<
										sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].haptic_dur_ul << ";STA" << l << ";H;MU" << endl;

								if(RAStas[l].ul_duration<optimal_dur_ul){
									logging_file << sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].haptic_dur_ul << ";"
																			<< sim_time-(optimal_dur_ul-RAStas[l].ul_duration) << ";STA" << l << ";V;MU" << endl;
									logging_file << sim_time-(optimal_dur_ul-RAStas[l].ul_duration) << ";"
											<< sim_time << ";STA" << l << ";P;MU" << endl;
									vid_delay_file << "logging done" << endl;
								}
								else
									logging_file << sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].haptic_dur_ul << ";"
										<< sim_time << ";STA" << l << ";V;MU" << endl;

								//					logging_file << sim_time-( bsrptime + SIFS + bsrtime + ul_firsttime*duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";" << sim_time << ";AP;" << send_media << endl;
							}

							else if (RAStas[l].send_media_mu.compare("V")==0){
								if(RAStas[l].ul_duration<optimal_dur_ul){
									logging_file << sim_time-( bsrptime + SIFS + bsrtime + duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";"
											<< sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].ul_duration << ";STA" << l << ";V;MU" << endl;
									logging_file << sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].ul_duration << ";"
											<< sim_time << ";STA" << l << ";P;MU" << endl;
								}

								else{
									logging_file << sim_time-( bsrptime + SIFS + bsrtime + duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";"
											<< sim_time << ";STA" << l << ";V;MU" << endl;
								}
							}


							else{
								if (RAStas[l].ul_duration<optimal_dur_ul){
									logging_file << sim_time-( bsrptime + SIFS + bsrtime + duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";" <<
											sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].haptic_dur_ul << ";STA" << l << ";H;MU" << endl;
									logging_file << sim_time-(optimal_dur_ul + SIFS + duration_multi_sta_back)+RAStas[l].haptic_dur_ul << ";"
											<< sim_time << ";STA" << l << ";P;MU" << endl;
								}

								else
									logging_file << sim_time-( bsrptime + SIFS + bsrtime + duration_tf + SIFS + optimal_dur_ul + SIFS + duration_multi_sta_back) << ";" << sim_time <<
									";STA" << l << ";" << RAStas[l].send_media_mu << ";MU" << endl;
								vid_delay_file << "logging done" << endl;
							}
							RAStas[l].ul_duration=0;
							RAStas[l].send_media_mu="";
						}
					}
					haptic_dur_ul_max=0;
				}


				if(inside_ulofdma){
					vid_delay_file << "Quitting UL-OFDMA!!  sim_time:  " << sim_time << endl;
					vid_delay_file << "Duration UL-OFDMA:  " << sim_time-ulofdma_start_time << endl;

//					inside_ulofdma=false;
					ulofdma_duration.push_back(sim_time-ulofdma_start_time);
				}

//				logging_file << sim_time-ulofdma_start_time << endl;

//				ul_ofdma_batch = 0;
//				dl_ofdma_batch = 0;

				// measuring the buffer occupancy after tx.
				temp_counter_stas=0;
				if(nSenders_ha==1){
					for (int s=0;s<pacQ_STA_ha.size();s++){
						temp_counter_stas+=pacQ_STA_ha[s].size();
					}
					STA_HA_queuesize.push_back(temp_counter_stas*1.0/pacQ_STA_ha.size());
				}
				else{
					for (int s=0;s<pacQ_STA_vi.size();s++){
						temp_counter_stas+=pacQ_STA_vi[s].size();
					}
					STA_VI_queuesize.push_back(temp_counter_stas*1.0/pacQ_STA_vi.size());
				}
			}


			else {

				vid_delay_file << "------ EDCA  ------" << endl;
				//this is a transmission by a contending STA using EDCA
				// Update sim_time and the no. of packets successfully sent; other steps such as storing sent sim_time, CW update done later
				//sta_file << "EDCA" << endl;
				int j;
				++edca_access;
				// HA-VI of same STA collision OR only STA-HA
				if (((nSenders_ha==1) && (nSenders_vi==1) && (ha_index==vi_index)) || ((nSenders_ha==1) && (nSenders_vi==0))){

					sta_file << "Same STA collision OR single STA" << endl;

					duration=HA_DURATION;
					packet_size=PACKET_SIZE_BWD_HA;
					pacQ_holder = &pacQ_STA_ha;
					retxQ_holder = &retxQ_STA_ha;
					retry_cnt_holder = &retry_cnt_STA_ha;
					retryCount = RETRY_COUNT_HA;
					media = "HA";
					for (int i = 0; i < nRAStas; i++) {
						j=100;
//						vid_delay_file << "inside for loop" << endl;
						if ((RAStas[i].bt_ha < 0) && (!(*pacQ_holder)[i].empty())){
//							vid_delay_file << "STA: " << i << "\tQ-size: " << (*pacQ_holder)[i].size() << endl;
//							if (i==0){
//								sta_file << "sim_time: " << sim_time << "    HA Won medium" << endl;
//							}
//							else{
//								sta_file << "Some other STA transmitting it" << endl;
//							}
							j=i;
//							vid_delay_file << "Selected STA: " << j << endl;
							break;
						}
					}
					delaystemp=&RAStas[j].delaysList.HA;
					delays_su=&RAStas[j].delays_su.HA;
					delays_mu=&RAStas[j].delays_mu.HA;
					// tracking the last packet sent
					lastSent_temp = &RAStas[j].lastSent_ha;
					accesstemp = &RAStas[j].nSuccAccess_HA;
					accesstemp_su = &RAStas[j].nSuccAccess_su_HA;
					ampdu_len=&ampdu_sta_su_HA;

				}

				// STA-VI has won the contention
				else{
					sta_file << "VI STA tx." << endl;
					duration=VI_DURATION;
					packet_size=FRAGMENT_SIZE;
					pacQ_holder = &pacQ_STA_vi;
					retxQ_holder = &retxQ_STA_vi;
					retry_cnt_holder = &retry_cnt_STA_vi;
					retryCount = RETRY_COUNT_VI;
					media = "VI";


					for (int i = 0; i < nRAStas; i++) {
						if ((RAStas[i].bt_vi < 0) && (!(*pacQ_holder)[i].empty())){
							j=i;
							break;
						}
					}



					lastSent_temp = &RAStas[j].lastSent_vi;
					delaystemp=&RAStas[j].delaysList.VI;
					delays_su=&RAStas[j].delays_su.VI;
					delays_mu=&RAStas[j].delays_mu.VI;
					accesstemp = &RAStas[j].nSuccAccess_VI;
					accesstemp_su = &RAStas[j].nSuccAccess_su_VI;
					ampdu_len=&ampdu_sta_su_VI;
				}


				// count the # samples in buffer
				RAStas[j].sampleCount = (*pacQ_holder)[j].size();
				sta_file << "Time: " << sim_time-AIFS_HA << "\tPreparing for EDCA of STA-" << j << "  sample count: " << RAStas[j].sampleCount << endl;
				vid_delay_file << "Time: " << sim_time-AIFS_HA << "\tPreparing for EDCA of STA-" << j << "  sample count: " << RAStas[j].sampleCount << endl;
//				if (RAStas[j].sampleCount>75){
//					vid_delay_file << "********* LOOK HERE ********* " << endl;
//					vid_delay_file << "Exiting" << endl;
//					exit(0);
//				}

				if (RAStas[j].sampleCount>0){

//					logging_file << "\Time: " <<sim_time << "\tSTA" << j <<"-success;     SU duration: ";
					RAStas[j].interAccess_ha.push_back(sim_time-RAStas[j].lastAccess_ha);
//					sta_interAccess_ha.push_back(sim_time-RAStas[j].lastAccess_ha);
//					sta_interAccess_ha_edca.push_back(sim_time-RAStas[j].lastAccess_ha);
					RAStas[j].lastAccess_ha = sim_time;


					RAStas[j].edca_ampdu_len =  std::min(RAStas[j].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, packet_size));
					RAStas[j].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[j].edca_ampdu_len, packet_size);
					sta_interAccess_ha.push_back(sim_time+RAStas[j].edca_ampdu_duration-RAStas[j].lastAccess_pois_ha);
					if (!RAStas[j].vid_last)
						sta_interAccess_su_ha.push_back(sim_time+RAStas[j].edca_ampdu_duration-RAStas[j].lastAccess_pois_ha);
					else
						sta_interAccess_su_ha_vid.push_back(sim_time+RAStas[j].edca_ampdu_duration-RAStas[j].lastAccess_pois_ha);

					RAStas[j].lastAccess_pois_ha = sim_time+RAStas[j].edca_ampdu_duration;
					RAStas[j].vid_last=false;
					RAStas[j].ampduLength_ha.push_back(RAStas[j].edca_ampdu_len);

					//ampdu_len += RAStas[j].edca_ampdu_len;
					(*ampdu_len) += RAStas[j].edca_ampdu_len;

					RAStas[j].nTx += RAStas[j].edca_ampdu_len;

					if(media.compare("VI")==0){
						vi_edca_count += RAStas[j].edca_ampdu_len;
					}
					if (j == 0){
						ul_zero_edca_ampdu += RAStas[j].edca_ampdu_len;
						++ul_zero_edca_access;
					}

					RAStas[j].queueheadTime = (*pacQ_holder)[j].front();
					(*lastSent_temp) = (*pacQ_holder)[j][RAStas[j].edca_ampdu_len-1];

					if (j==0){
						sta_file << "sending from " << (*pacQ_holder)[j].front() << " to " << (*pacQ_holder)[j].front()+RAStas[j].edca_ampdu_len-1 << "  Q ends: " << (*pacQ_holder)[j].back() << endl;
					}
					(*pacQ_holder)[j].erase((*pacQ_holder)[j].begin(), (*pacQ_holder)[j].begin()+RAStas[j].edca_ampdu_len);

					// remove retry details of sent packets
					for (int m=0;m<(*retxQ_holder)[j].size();m++){
						if ((*lastSent_temp)>=(*retxQ_holder)[j][m]){
							++RAStas[j].count_remove_sent;
						}
					}

//					if (media.compare("VI")==0){
//						printf("\nSTA %d: Removed %d %s frames \t Queue length %d\n", j, RAStas[j].edca_ampdu_len, media.c_str(),
//														pacQ_STA_vi[j].size());
//						if (j==0){
//							printf("\n\n------------- VI retry count: sending-removing -------------\n");
//							printf("Removing %d entries\n", (RAStas[j].count_remove_sent));
//						}
//					}

					// ----------------------------------------------------
//					if ((j==0) && (media.compare("VI")==0)){
//						staO_file << "\ntime: " <<  sim_time << "   Transmitting until " << RAStas[j].queueheadTime+(RAStas[j].edca_ampdu_len-1)*duration << " & hence flushing " << RAStas[j].count_remove_sent << " entries from RTRQ" << endl;
//						cout << "\ntime: " <<  sim_time << "   Transmitting until " << RAStas[j].queueheadTime+(RAStas[j].edca_ampdu_len-1)*duration << " & hence flushing " << RAStas[j].count_remove_sent << " entries from RTRQ" << endl;
//
//					}
					// ----------------------------------------------------

					if (j==0){
						//sta_file << "Before removing Retx Q ends: " <<  endl; // (*retxQ_holder)[j].back() <<
					}
					(*retxQ_holder)[j].erase((*retxQ_holder)[j].begin(), (*retxQ_holder)[j].begin()+ RAStas[j].count_remove_sent);
					(*retry_cnt_holder)[j].erase((*retry_cnt_holder)[j].begin(), (*retry_cnt_holder)[j].begin()+RAStas[j].count_remove_sent);

					if (j==0){
						if (((*retxQ_holder)[j].size()>0)){
							sta_file << "After removing Retx Q ends: " << (*retxQ_holder)[j].back() << endl;
						}
					}
					RAStas[j].count_remove_sent=0;
					RAStas[j].delay = sim_time+(RAStas[j].edca_ampdu_len*packet_size>STA_RTS_THRESHOLD)*(RTS_TIME+CTS_TIME)+RAStas[j].edca_ampdu_duration-RAStas[j].queueheadTime;
					RAStas[j].hap_frames_sent += RAStas[j].edca_ampdu_len;

					total_hap_frames += RAStas[j].edca_ampdu_len;

					// record the delays
					for (int z=0;z<RAStas[j].edca_ampdu_len;z++){ //
						// w/o accounting for jitter buffer delay
						RAStas[j].sampleAccessDelay.push_back((RAStas[j].delay-z*duration));

						// accounting for jitter buffer delay
						(*delaystemp).push_back((RAStas[j].delay));
//						if (nRAStas==5 && (media.compare("VI")==0)){
//							delayFile << sim_time << "\t" << RAStas[j].delay-z*duration << endl;
//						}
						if(RAStas[j].ulofdma_just_sta && (media.compare("HA")==0)){
							ulofdmadelay_sta.push_back(RAStas[j].delay);
						}
						else if ((!RAStas[j].ulofdma_just_sta) && (media.compare("HA")==0)){
							nonulofdmadelay_sta.push_back(RAStas[j].delay);
						}
						else if(media.compare("HA")==0){
							otherdelay.push_back(RAStas[j].delay);
						}
						(*delays_su).push_back((RAStas[j].delay-z*duration));
//						if (nSenders_ha!=1){
//							printf("EDCA-VI --- STA %d \t Media: %s \t sim_time: %d \t Sample: %d \t AMPDU: %d \t duration: %d \t max_duration: %d \t delay: %d\n",
//															j, media.c_str(), sim_time, RAStas[j].queueheadTime+z*duration, RAStas[j].edca_ampdu_len, RAStas[j].edca_ampdu_duration,
//															RAStas[j].edca_ampdu_duration, (*delaystemp).back());
//						}

//									RAStas[].queueheadTime/1000 << "    delay:" << RAStas[i].delay-z*1000 << "\n";

						if (j==0){
							sta_file << RAStas[j].queueheadTime*1.0/duration+z << "\t" <<
											   RAStas[j].queueheadTime*1.0/duration+z+(*delaystemp).back()*1.0/duration << "\tMedia: " << media <<"\n";
						}
//							ul_zero_edca_delay.push_back((*delaystemp).back());
//						}
						//output_file_STA << "STA" << i << "    sim_time:" << sim_time << "    AMPDU:" << RAStas[i].edca_ampdu_len << "    queuehead:" <<
						//			RAStas[i].queueheadTime/1000 << "    delay:" << RAStas[i].delay-z*1000 << "\n";

					}
					RAStas[j].ulofdma_just_sta=false;

					if ((j==0) && (media.compare("VI") == 0)){
						video_file << "**** Tx. done ***** \t sim_time: " << sim_time << "   Size: " << (*pacQ_holder)[j].size() << endl;
					}

					sta_file << "STA-" << j << "   EDCA dur: " << RAStas[j].edca_ampdu_duration << "   sim_time from " << sim_time << " to " ;

					time_overhead += SIFS + duration_back;
					logging_file << sim_time-AIFS_HA << ";";
					sim_time = sim_time + RAStas[j].edca_ampdu_duration + SIFS + duration_back;


//					logging_file << RAStas[j].edca_ampdu_duration + SIFS + duration_back << endl;
					if (RAStas[j].edca_ampdu_len * packet_size > STA_RTS_THRESHOLD){
						sim_time = sim_time + RTS_TIME + CTS_TIME;
						time_overhead += RTS_TIME + CTS_TIME;
						++rts_cts_count_noCollision;
					}
					logging_file << sim_time << ";STA" << j << ";H;SU" << endl;
					sta_file << sim_time << endl;

					sta_file << "Q-size after tx. " << (*pacQ_holder)[j].size() << endl;

					APSta.time_staSend += RAStas[j].edca_ampdu_duration + SIFS + duration_back;
					APSta.time_staDataSend += RAStas[j].edca_ampdu_duration;
					//cout << "time5: " << sim_time << endl;

					if (nSenders_ha==1){
						// measuring the buffer occupancy after tx.
						STA_HA_queuesize.push_back((*pacQ_holder)[j].size());
					}
					else{
						// measuring the buffer occupancy after tx.
						STA_VI_queuesize.push_back((*pacQ_holder)[j].size());
					}
					txtime_sta.push_back(RAStas[j].edca_ampdu_duration);


					if (RAStas[j].edca_ampdu_len<0){
						printf("AMPDU neg. value");
						exit(0);
					}

					++(*accesstemp);
					++(*accesstemp_su);

					RAStas[j].cw_ha=0;


//					RAStas[j].nSuccAccesses += 1;
//					RAStas[j].nSuccAccesses_su += 1;
					//sta_maxbt += RAStas[i].max_bt;
					//RAStas[i].max_bt=0;

				}
				vid_delay_file << "Finishing up EDCA with duration: " << RAStas[j].edca_ampdu_duration + SIFS + duration_back << endl;
			}
		}


		// case of collisions
		else {
			vid_delay_file << "\n Time: " << sim_time << "   Case of collisions involving " << nSenders_ha << " devices" << endl;
			++numCollisions;
			// HA-VI belonging to different devices
			if ((nSenders_ha==1 && nSenders_vi==1)){

				vid_delay_file << "Will never come here...." << endl;
				max_duration = 0;
				sta_file << "Diff. device collision: HA and VI" << endl;
				// VI-STA
				RAStas[vi_index].sampleCount = pacQ_STA_vi[vi_index].size();
				RAStas[vi_index].edca_ampdu_len =  std::min(RAStas[vi_index].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, FRAGMENT_SIZE));
				RAStas[vi_index].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[vi_index].edca_ampdu_len, FRAGMENT_SIZE);

				pacQ_holder=&pacQ_STA_vi;
				retxQ_holder = &retxQ_STA_vi;
				retry_cnt_holder = &retry_cnt_STA_vi;
				media = "VI";

				AC_packets = updateRetryInfo(vi_index, RAStas[vi_index].edca_ampdu_len-1, RETRY_COUNT_VI, true, sim_time);
				RAStas[vi_index].dropped_vi += AC_packets.vi;
				max_duration = (RAStas[vi_index].edca_ampdu_len*FRAGMENT_SIZE > STA_RTS_THRESHOLD) ?
						RTS_TIME+CTS_TIME : RAStas[vi_index].edca_ampdu_duration;

				// HA-STA
				if (!ap_wins){
					sta_file << "HA-STA" << endl;
					RAStas[ha_index].sampleCount = pacQ_STA_vi[ha_index].size();
					RAStas[ha_index].edca_ampdu_len =  std::min(RAStas[ha_index].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, PACKET_SIZE_BWD_HA));
					RAStas[ha_index].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[ha_index].edca_ampdu_len, PACKET_SIZE_BWD_HA);

					pacQ_holder=&pacQ_STA_ha;
					retxQ_holder = &retxQ_STA_ha;
					retry_cnt_holder = &retry_cnt_STA_ha;
					media = "HA";

					// call function to update RTRQ table entries
					AC_packets = updateRetryInfo(ha_index, RAStas[ha_index].edca_ampdu_len-1, RETRY_COUNT_HA, true, sim_time);
					RAStas[ha_index].dropped_ha += AC_packets.ha;

					if (RAStas[ha_index].edca_ampdu_len*PACKET_SIZE_BWD_HA<STA_RTS_THRESHOLD){
						max_duration = (max_duration>RAStas[ha_index].edca_ampdu_duration) ? max_duration : RAStas[ha_index].edca_ampdu_duration;
					}
					else{
						max_duration = (max_duration > RTS_TIME+CTS_TIME) ? max_duration : RTS_TIME+CTS_TIME;
					}
//					max_duration = (RAStas[vi_index].edca_ampdu_duration>=RAStas[ha_index].edca_ampdu_duration) ?
//							RAStas[vi_index].edca_ampdu_duration : RAStas[ha_index].edca_ampdu_duration;

				}

				// HA-AP
				else{
					APSta.num_dl_STAs=0;
					APSta.max_duration=0;
					APSta.dl_stas.clear();
					//printf("\n-------------------------------------------\n");
					vid_delay_file << "\nAP collision\n" << endl;

					packet_size=PACKET_SIZE_FWD_HA;
					pacQ_holder=&pacQ_AP_ha;
					retry_cnt_holder=&retry_cnt_AP_ha;
					retxQ_holder=&retxQ_AP_ha;
					retryCount=RETRY_COUNT_HA;
					media = "HA";




					ampdu_DL_currentsize.clear();
					ampdu_DL_currentduration.clear();

					APSta.dl_stas.clear();
					for (int s=0;s<(*pacQ_holder).size();s++){
						APSta.queuesize = (*pacQ_holder)[s].size();
						if(APSta.queuesize>0){
							++APSta.num_dl_STAs;
							APSta.dl_stas.push_back(true);
						}
						else{
							APSta.dl_stas.push_back(false);
						}
					}

//					ORIGINAL
					if (ofdma_bw_mode){
						if (APSta.num_dl_STAs>=3){
							tone = RU_SIZE_242_TONES;
						}
						else if (APSta.num_dl_STAs==2){
							tone = RU_SIZE_484_TONES;
						}
						else if (APSta.num_dl_STAs==1){
							tone = RU_SIZE_996_TONES;
						}
					}

					else{


						if (APSta.num_dl_STAs>8){
							tone = RU_SIZE_52_TONES;
						}
						else if (APSta.num_dl_STAs>4){
							tone = RU_SIZE_106_TONES;
						}
						//					if (APSta.num_dl_STAs>=8){
						//						tone = RU_SIZE_106_TONES;
						//					}
						else if (APSta.num_dl_STAs>=3){
							tone = RU_SIZE_242_TONES;
						}
						else if (APSta.num_dl_STAs==2){
							tone = RU_SIZE_484_TONES;
						}
						else if (APSta.num_dl_STAs==1){
							tone = RU_SIZE_996_TONES;
						}
					}



					APSta.dl_stas_ru.clear();
					for(int i=0;i<APSta.dl_stas.size();i++){
						if (APSta.dl_stas[i]){
							APSta.dl_stas_ru.push_back(tone);
						}
						else{
							APSta.dl_stas_ru.push_back(0);
						}
					}

					APSta.current_size.clear();
					for (int s=0;s<(*pacQ_holder).size();s++){
						APSta.queuesize=(*pacQ_holder)[s].size();

						queue_size = APSta.queuesize;
						APSta.current_size.push_back(std::min(queue_size, getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], max_ofdma_duration, packet_size)));
						APSta.current_duration = getOfdmaAMpduDuration (mcs, APSta.dl_stas_ru[s], 0, 0, APSta.current_size[s], packet_size, bw);
						//					cout << "sim_time:  " << sim_time << "\t latest size: " << APSta.current_size.back() << "\tmedia: " << media.c_str() << "\tq size " << queue_size << "\tQ non-empty?: " << APSta.dl_stas[s] <<
						//							"\t OFDMA length: " << getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], MAX_PPDU_DURATION_US, packet_size) << "\tDL RU: " << APSta.dl_stas_ru[s] << endl;
						//APSta.index_ap = APSta.current_size.back()-1;
						//					printf("  AP \t Media: %s \t AMPDU %d \t duration %d\n", media.c_str(), APSta.current_size[s], APSta.current_duration);

						if(APSta.current_duration>APSta.max_duration){
							APSta.max_duration=APSta.current_duration;
						}

						// call function to update the retry table entries
						AC_packets = updateRetryInfo(s, APSta.current_size.back()-1, retryCount, false, sim_time);
						APSta.dropped_ha += AC_packets.ha;

						//					cout << "AP: " << s << "   Dropped: " << APSta.dropped_vi << " packets" << endl;
					}

//					max_duration = (RAStas[vi_index].edca_ampdu_duration>=APSta.max_duration) ?
//							RAStas[vi_index].edca_ampdu_duration : APSta.max_duration;
				}
				// call function to update RTRQ table entries

			}

			// if there is at least 1 HA device
			if (nSenders_ha>1){
				vid_delay_file << "At least 1 STA involved...." << endl;
				sta_file << "Multiple HA STAs: " << nSenders_ha << endl;
				nCollisions += 1;
				max_duration=0;
				// at least 1 HA device VI-STA
				if(nSenders_vi>0){
					vid_delay_file << "Will never come here...." << endl;
					++numVidCollisions;
					sta_file << nSenders_vi << " VI STAs" << endl;
					// if STAs have VI that won then CW should be expanded and RTRQ updated
					for (int z=0; z<nRAStas; z++){
						if ((RAStas[z].bt_vi<0) && (!pacQ_STA_vi[z].empty())){
							RAStas[z].sampleCount = pacQ_STA_vi[z].size();
							RAStas[z].edca_ampdu_len =  std::min(RAStas[z].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, FRAGMENT_SIZE));
							RAStas[z].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[z].edca_ampdu_len, FRAGMENT_SIZE);

							pacQ_holder=&pacQ_STA_vi;
							retxQ_holder = &retxQ_STA_vi;
							retry_cnt_holder = &retry_cnt_STA_vi;
							media = "VI";

							// call function to update RTRQ table entries
							if (!((RAStas[z].bt_ha<0) && (pacQ_STA_ha[z].size()))){
								AC_packets = updateRetryInfo(z, RAStas[z].edca_ampdu_len-1, RETRY_COUNT_VI, true, sim_time);
								RAStas[z].dropped_ha += AC_packets.ha;
								RAStas[z].dropped_vi += AC_packets.vi;
								sta_file << "Q-size VI: " << RAStas[z].edca_ampdu_len << " AMPDU dur: " << RAStas[z].edca_ampdu_duration << endl;
								sta_file << "dur from VI: " << RAStas[z].edca_ampdu_duration << "  curr max.: " << max_duration << endl;

								if (RAStas[z].edca_ampdu_len*FRAGMENT_SIZE < STA_RTS_THRESHOLD){
									max_duration = (max_duration>RAStas[z].edca_ampdu_duration) ? max_duration : RAStas[z].edca_ampdu_duration;
									sta_file << "changing max to: " << max_duration << endl;
								}
								else{
									max_duration = (max_duration > RTS_TIME+CTS_TIME) ? max_duration : RTS_TIME+CTS_TIME;
								}



//								if (RAStas[z].edca_ampdu_duration > max_duration){
//									max_duration=RAStas[z].edca_ampdu_duration;
//									sta_file << "changing max to: " << max_duration << endl;
//								}
							}

							else{
								sta_file << "STA-" << z << "   skipping unnecessary VI CE bloating" << endl;
							}
						}
					}
				}

				sim_time += AIFS_HA;

				// HA devices
				// HA-AP
				if (ap_wins){
					APSta.num_dl_STAs=0;
					APSta.max_duration=0;
					APSta.dl_stas.clear();
					//printf("\n-------------------------------------------\n");
					printf("\nAP collision\n");
//					logging_file << "\nTime: " << sim_time << "\tAP-collision   --- duration: ";
					vid_delay_file << "AP involved..." << endl;
					++num_collisions;
					vid_delay_file << "Changing num_collisions to " << num_collisions << endl;

					packet_size=PACKET_SIZE_FWD_HA;
					pacQ_holder=&pacQ_AP_ha;
					retry_cnt_holder=&retry_cnt_AP_ha;
					retxQ_holder=&retxQ_AP_ha;
					retryCount=RETRY_COUNT_HA;
					media = "HA";

					ampdu_DL_currentsize.clear();
					ampdu_DL_currentduration.clear();

					APSta.dl_stas.clear();
					queue_size=0;
					for (int s=0;s<(*pacQ_holder).size();s++){
						queue_size += (*pacQ_holder)[s].size();
						if((*pacQ_holder)[s].size()>0){
							++APSta.num_dl_STAs;
							APSta.dl_stas.push_back(true);
						}
						else{
							APSta.dl_stas.push_back(false);
						}
					}


//					ORIGINAL
					if (ofdma_bw_mode){
						if (APSta.num_dl_STAs>=3){
							tone = RU_SIZE_242_TONES;
						}
						else if (APSta.num_dl_STAs==2){
							tone = RU_SIZE_484_TONES;
						}
						else if (APSta.num_dl_STAs==1){
							tone = RU_SIZE_996_TONES;
						}
					}

					else{
						if (APSta.num_dl_STAs>8){
							tone = RU_SIZE_52_TONES;
						}
						else if (APSta.num_dl_STAs>4){
							tone = RU_SIZE_106_TONES;
						}
						//					if (APSta.num_dl_STAs>=8){
						//						tone = RU_SIZE_106_TONES;
						//					}
						else if (APSta.num_dl_STAs>=3){
							tone = RU_SIZE_242_TONES;
						}
						else if (APSta.num_dl_STAs==2){
							tone = RU_SIZE_484_TONES;
						}
						else if (APSta.num_dl_STAs==1){
							tone = RU_SIZE_996_TONES;
						}
					}


//					if (APSta.num_dl_STAs>=8){
//						tone = RU_SIZE_106_TONES;
//					}
//					else if (APSta.num_dl_STAs>=3){
//						tone = RU_SIZE_242_TONES;
//					}
//					else if (APSta.num_dl_STAs==2){
//						tone = RU_SIZE_484_TONES;
//					}
//					else if (APSta.num_dl_STAs==1){
//						tone = RU_SIZE_996_TONES;
//					}


					APSta.dl_stas_ru.clear();

					for(int i=0;i<APSta.dl_stas.size();i++){
						if (APSta.dl_stas[i]){
							APSta.dl_stas_ru.push_back(tone);
						}
						else{
							APSta.dl_stas_ru.push_back(0);
						}
					}
					APSta.current_size.clear();
					for (int s=0;s<(*pacQ_holder).size();s++){
						APSta.queuesize=(*pacQ_holder)[s].size();
//						queue_size = APSta.queuesize;
						APSta.current_size.push_back(std::min(APSta.queuesize, getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], max_ofdma_duration, packet_size)));
						APSta.current_duration = getOfdmaAMpduDuration (mcs, APSta.dl_stas_ru[s], 0, 0, APSta.current_size[s], packet_size, bw);

						//					cout << "sim_time:  " << sim_time << "\t latest size: " << APSta.current_size.back() << "\tmedia: " << media.c_str() << "\tq size " << queue_size << "\tQ non-empty?: " << APSta.dl_stas[s] <<
						//							"\t OFDMA length: " << getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], MAX_PPDU_DURATION_US, packet_size) << "\tDL RU: " << APSta.dl_stas_ru[s] << endl;
						//APSta.index_ap = APSta.current_size.back()-1;
						//					printf("  AP \t Media: %s \t AMPDU %d \t duration %d\n", media.c_str(), APSta.current_size[s], APSta.current_duration);
						if (s==0){
							vid_delay_file << "AP collision duration: " << APSta.current_duration << endl;
							vid_delay_file << "Current size: " << queue_size*packet_size << endl;
						}

						if (queue_size*packet_size <= AP_RTS_THRESHOLD){
							max_duration = (max_duration>APSta.current_duration) ? max_duration : APSta.current_duration;
							sta_file << "changing max to: " << max_duration << endl;
							if (s==0){
								vid_delay_file << "At AP's end: Less than threshold" << endl;
								vid_delay_file << "Temp. collision duration at AP: " << max_duration << endl;
							}
						}

						else{
							max_duration = (max_duration > RTS_TIME+CTS_TIME) ? max_duration : RTS_TIME+CTS_TIME;
							if (s==0){
								vid_delay_file << "At AP's end: more than threshold" << endl;
								vid_delay_file << "Temp. collision duration at AP: " << max_duration << endl;
							}
						}



//						if(APSta.current_duration>max_duration){
//							max_duration=APSta.current_duration;
//						}

						// call function to update the retry table entries
						AC_packets = updateRetryInfo(s, APSta.current_size.back()-1, retryCount, false, sim_time);
						APSta.dropped_ha += AC_packets.ha;

						sta_file << "Q-size HA: " << APSta.current_size.back() << " AMPDU dur: " << APSta.current_duration << endl;
						sta_file << "dur from HA: " << APSta.current_duration << "  curr max.: " << max_duration << endl;


						//					cout << "AP: " << s << "   Dropped: " << APSta.dropped_vi << " packets" << endl;
					}

					ap_collision_duration=max_duration;
					logging_file << sim_time  << ";";
//					sim_time = sim_time + max_duration + SIFS + duration_back;
					logging_file << sim_time+ap_collision_duration+SIFS+duration_back << ";" << "AP;C;-" << endl;
					vid_delay_file << ap_collision_duration << endl;
				}

				// HA-STA: other STAs (if any) that have won
				for (int i = 0; i < nRAStas; i++) {
					pacQ_holder=&pacQ_STA_ha;
					retxQ_holder = &retxQ_STA_ha;
					retry_cnt_holder = &retry_cnt_STA_ha;
					media = "HA";

					if ((RAStas[i].bt_ha < 0) && (!(*pacQ_holder)[i].empty())){
						sta_file << "HA-STA collision: " << i << endl;
						temp_sta_index = i;
						vid_delay_file << "STA: " << i << " also collided" << endl;
//						logging_file << "\nTime: " << sim_time << "\tSTA" << i << "-collision --- duration: ";
						RAStas[i].sampleCount = (*pacQ_holder)[i].size();
						RAStas[i].edca_ampdu_len =  std::min(RAStas[i].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, PACKET_SIZE_BWD_HA));
						RAStas[i].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[i].edca_ampdu_len, PACKET_SIZE_BWD_HA);

						// call function to update retry table entries
						AC_packets = updateRetryInfo(i, RAStas[i].edca_ampdu_len-1, retryCount, true, sim_time);
						RAStas[i].dropped_ha += AC_packets.ha;
						RAStas[i].dropped_vi += AC_packets.vi;
						sta_file << "Q-size HA: " << RAStas[i].edca_ampdu_len << " AMPDU dur: " << RAStas[i].edca_ampdu_duration << endl;
						sta_file << "dur from HA: " << RAStas[i].edca_ampdu_duration << "  curr max.: " << max_duration << endl;

//						if (RAStas[i].edca_ampdu_len*PACKET_SIZE_BWD_HA < RTS_THRESHOLD){
//							max_duration = (max_duration>RAStas[i].edca_ampdu_duration) ? max_duration : RAStas[i].edca_ampdu_duration;
//							sta_file << "changing max to: " << max_duration << endl;
//						}

						vid_delay_file << "Current size: " << RAStas[i].edca_ampdu_len*PACKET_SIZE_BWD_HA << endl;
						if (RAStas[i].edca_ampdu_len*PACKET_SIZE_BWD_HA > STA_RTS_THRESHOLD){
							vid_delay_file << "Adding RTS and CTS" << endl;
							max_duration = (max_duration > RTS_TIME+CTS_TIME) ? max_duration : RTS_TIME+CTS_TIME;
							vid_delay_file << "Temp. collision duration at STA " << i << ": " << max_duration << endl;
							RAStas[i].sta_collision_duration = RAStas[i].edca_ampdu_duration+RTS_TIME+CTS_TIME;
						}
						else{
							vid_delay_file << "Not adding RTS and CTS" << endl;
							max_duration = (max_duration>RAStas[i].edca_ampdu_duration) ? max_duration : RAStas[i].edca_ampdu_duration;
							vid_delay_file << "EDCA collision duration at STA " << i << ": " << RAStas[i].edca_ampdu_duration << endl;
							vid_delay_file << "Temp. collision duration at STA " << i << ": " << max_duration << endl;
							RAStas[i].sta_collision_duration = RAStas[i].edca_ampdu_duration;
						}

						logging_file << sim_time << ";" << sim_time+
										RAStas[i].sta_collision_duration+SIFS+duration_back << ";STA" << i <<";C;-" << endl ;

//						if (RAStas[i].edca_ampdu_duration > max_duration){
//							max_duration = RAStas[i].edca_ampdu_duration;
//							sta_file << "changing max to: " << max_duration << endl;
//						}
					}
				}

			}

			else if (nSenders_vi>1){
				vid_delay_file << "Will never come here..." << endl;
				++numVidCollisions;
				sta_file << nSenders_vi << " only VI STAs" << endl;
				// if STAs have VI that won then CW should be expanded and RTRQ updated
				for (int z=0; z<nRAStas; z++){
					if ((RAStas[z].bt_vi<0) && (!pacQ_STA_vi[z].empty())){
						RAStas[z].sampleCount = pacQ_STA_vi[z].size();
						RAStas[z].edca_ampdu_len =  std::min(RAStas[z].sampleCount, getEdcaAMpduLength(mcs, bw, max_ofdma_duration, FRAGMENT_SIZE));
						RAStas[z].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[z].edca_ampdu_len, FRAGMENT_SIZE);

						pacQ_holder=&pacQ_STA_vi;
						retxQ_holder = &retxQ_STA_vi;
						retry_cnt_holder = &retry_cnt_STA_vi;
						media = "VI";

						// call function to update RTRQ table entries
						AC_packets = updateRetryInfo(z, RAStas[z].edca_ampdu_len-1, RETRY_COUNT_VI, true, sim_time);
						RAStas[z].dropped_ha += AC_packets.ha;
						RAStas[z].dropped_vi += AC_packets.vi;
						sta_file << "Q-size VI: " << RAStas[z].edca_ampdu_len << " AMPDU dur: " << RAStas[z].edca_ampdu_duration << endl;
						sta_file << "dur from VI: " << RAStas[z].edca_ampdu_duration << "  curr max.: " << max_duration << endl;

						if (RAStas[z].edca_ampdu_len*FRAGMENT_SIZE < STA_RTS_THRESHOLD){
							max_duration = (max_duration>RAStas[z].edca_ampdu_duration) ? max_duration : RAStas[z].edca_ampdu_duration;
							sta_file << "changing max to: " << max_duration << endl;
						}
						else{
							max_duration = (max_duration > RTS_TIME+CTS_TIME) ? max_duration : RTS_TIME+CTS_TIME;
						}

//						if (RAStas[z].edca_ampdu_duration > max_duration){
//							max_duration=RAStas[z].edca_ampdu_duration;
//							sta_file << "changing max to: " << max_duration << endl;
//						}
					}
				}
			}

			//sta_file << "AIFA-HA: sim_time from " << sim_time << " to " << sim_time + AIFS_HA << endl;
			//sim_time += AIFS_HA;

			vid_delay_file << "Collision duration: " << max_duration << " ... Adding " << max_duration + SIFS + duration_back  << " to time " << endl;

//			logging_file << sim_time  << ";";
			sim_time = sim_time + max_duration + SIFS + duration_back;
//			logging_file << sim_time-max_duration+ap_collision_duration << ";" << "AP;C;-" << endl;
//			vid_delay_file << ap_collision_duration << endl;
//			logging_file << max_duration + SIFS + duration_back << "\n" << endl;

//			logging_file << sim_time-(max_duration + SIFS + duration_back) << ";" << sim_time-max_duration+
//				RAStas[temp_sta_index].sta_collision_duration << ";STA" << temp_sta_index <<";C;-" << endl ;
			overhead_collision += max_duration + SIFS + duration_back;
			APSta.time_collision+= max_duration + SIFS + duration_back;

			//			cout << "time8: " << sim_time << "\tmax_dur: " << max_duration << "\tSTA: " << max_duration_STA << "\tcurr: " << APSta.current_duration << "  media: " << media << endl;
			APSta.max_duration=0;


//		}

//			// no HA STAs and at least 2 VI STAs
//			else if ((nSenders_ha==0) && (nSenders_vi>1)){
//				sta_file << "AIFA-VI: sim_time from " << sim_time << " to " << sim_time + AIFS_VI << endl;
//				sim_time += AIFS_VI;
////				cout << "time7: " << sim_time << endl;
//
//				packet_size=PACKET_SIZE_BWD_VI;
//				pacQ_holder=&pacQ_STA_vi;
//				retry_cnt_holder=&retry_cnt_STA_vi;
//				retxQ_holder=&retxQ_STA_vi;
//				retryCount=RETRY_COUNT_VI;
//				media = "VI";
//			}

//			sim_time = sim_time + AIFS_HA;
			//APSta.max_duration=0;
			APSta.num_dl_STAs=0;
//			APSta.dl_stas.clear();
//			APSta.dl_stas_ru.clear();
			dl_stas.clear();

		}
			//if the AP is among the transmitter and is using UL OFDMA, it will stop any transmission
			//after sending the TF so the wasted sim_time is always equal to a station transmission duration
			//if the AP is using DL OFDMA or DL MU-MIMO, it must not come here (actually we consider no collisions in these cases)


			// sim_time should be forwarded by the maximum of duration across STAs and AP
			//max_duration_STA = 0;

			// STA part

//			for (int i = 0; i < nRAStas; i++) {
//				if ((RAStas[i].bt_ha < 0) && (!(*pacQ_holder)[i].empty())){
//					RAStas[i].sampleCount = (*pacQ_holder)[i].size();
//					RAStas[i].edca_ampdu_len =  std::min(RAStas[i].sampleCount, getEdcaAMpduLength(mcs, bw, MAX_PPDU_DURATION_US, packet_size));
//					RAStas[i].edca_ampdu_duration = getEdcaAMpduDuration (mcs, bw, RAStas[i].edca_ampdu_len, packet_size);
//
////					printf("STA %d \t Media: %s \t AMPDU %d \t duration %d\n", i,media.c_str(), RAStas[i].edca_ampdu_len, RAStas[i].edca_ampdu_duration);
//
////					if (i==0 && media.compare("VI")==0){
////						printf ("\nDropped ---->  %d\t", RAStas[i].dropped_ha);
////					}
//					// call function to update retry table entries
//					AC_packets = updateRetryInfo(i, RAStas[i].edca_ampdu_len-1, retryCount, true, sim_time);
//					RAStas[i].dropped_ha += AC_packets.ha;
//					RAStas[i].dropped_vi += AC_packets.vi;
//
////					if (i==0 && media.compare("HA")==0){
////						printf ("%d\n", RAStas[i].dropped_ha);
////					}
////					if empty, push new entries
////					if ((*retry_cnt_holder)[i].empty()){
////						(*retry_cnt_holder)[i].push_back(1);
////						(*retxQ_holder)[i].push_back((*pacQ_holder)[i][RAStas[i].edca_ampdu_len-1]);
////
////						if (media.compare("VI")==0){
////							if (i==0){
////								printf("\n\n------------- VI retry count: Adding initial -------------\n");
////								for (int x=0; x<(*retry_cnt_holder)[i].size(); x++){
////									printf("%lld %d \n", (*retxQ_holder)[i].back(), (*retry_cnt_holder)[i].back());
////								}
////							}
////						}
////					}
////
////					else {
////						// update existing entries
////						if (((*pacQ_holder)[i][RAStas[i].edca_ampdu_len-1]>=(*retxQ_holder)[i].back())){
////							for (int k=0;k<(*retxQ_holder)[i].size();k++){
////								(*retry_cnt_holder)[i][k] += 1;
////							}
////							if (media.compare("VI")==0){
////								if (i==0){
////									printf("\n\n------------- VI retry count: Updating -------------\n");
////									for (int x=0; x<(*retry_cnt_holder)[i].size(); x++){
////										printf("%lld %d \t %d %d\n", (*retxQ_holder)[i].back(), (*retry_cnt_holder)[i].back());									}
////								}
////							}
////						}
////						// add new entries
////						if (((*pacQ_holder)[i][RAStas[i].edca_ampdu_len-1]>(*retxQ_holder)[i].back())){
////							(*retxQ_holder)[i].push_back((*pacQ_holder)[i][RAStas[i].edca_ampdu_len-1]);
////							(*retry_cnt_holder)[i].push_back(1);
////
////							if (media.compare("VI")==0){
////								if (i==0){
////									printf("\n\n------------- VI retry count: Adding -------------\n");
////									for (int x=0; x<(*retry_cnt_holder)[i].size(); x++){
////										printf("%lld %d \t %d %d\n", (*retxQ_holder)[i].back(), (*retry_cnt_holder)[i].back());									}
////								}
////							}
////						}
////
////
////						// delete MPDUs if retry count threshold is exceeded
////						if ((*retry_cnt_holder)[i].front()>retryCount){
////							for(int y=0;y<(*pacQ_holder)[i].size();y++){
////								if ((*retxQ_holder)[i].front()>=(*pacQ_holder)[i][y]){
////									++RAStas[i].count_remove_drop;
////								}
////								else{
////									break;
////								}
////							}
////
////							if (media.compare("VI")==0){
////								if (i==0){
////									printf("\n\n------------- VI retry count: Discarding -------------\n");
////									for (int x=0; x<(*retry_cnt_holder)[i].size(); x++){
////										printf("%lld %d \t %d %d\n", (*retxQ_holder)[i].back(), (*retry_cnt_holder)[i].back());									}
////								}
////							}
////
////							(*pacQ_holder)[i].erase((*pacQ_holder)[i].begin(), (*pacQ_holder)[i].begin()+RAStas[i].count_remove_drop);
////							(*retry_cnt_holder)[i].erase((*retry_cnt_holder)[i].begin(), (*retry_cnt_holder)[i].begin()+1);
////							(*retxQ_holder)[i].erase((*retxQ_holder)[i].begin(), (*retxQ_holder)[i].begin()+1);
////							if (nSenders_ha>1){
////								RAStas[i].dropped_ha +=RAStas[i].count_remove_drop;
////							}
////							else if ((nSenders_ha==0) && (nSenders_vi>0)){
////								RAStas[i].dropped_vi +=RAStas[i].count_remove_drop;
////							}
////
////							RAStas[i].count_remove_drop=0;
////						}
////					}
//
//					if (RAStas[i].edca_ampdu_duration > max_duration_STA){
//						max_duration_STA = RAStas[i].edca_ampdu_duration;
//					}
//				}
//			}

			// AP part
//			if (apCollision && nSenders_ha>0){
//				APSta.num_dl_STAs=0;
//				APSta.max_duration=0;
//				APSta.dl_stas.clear();
//				//printf("\n-------------------------------------------\n");
//				printf("\nAP collision\n");
//
////				cout << "HA senders: " << nSenders_ha << " VI senders: " << nSenders_vi << endl;
//
//				packet_size=PACKET_SIZE_FWD_HA;
//				pacQ_holder=&pacQ_AP_ha;
//				retry_cnt_holder=&retry_cnt_AP_ha;
//				retxQ_holder=&retxQ_AP_ha;
//				retryCount=RETRY_COUNT_HA;
//				media = "HA";
//
////				if (nSenders_ha>1){
////					packet_size=PACKET_SIZE_HA;
////					pacQ_holder=&pacQ_AP_ha;
////					retry_cnt_holder=&retry_cnt_AP_ha;
////					retxQ_holder=&retxQ_AP_ha;
////					retryCount=RETRY_COUNT_HA;
////					media = "HA";
////				}
////				// no HA STAs and at least 2 VI STAs
////				else if ((nSenders_ha==0) && (nSenders_vi>0)){
////					packet_size=PACKET_SIZE_VI;
////					pacQ_holder=&pacQ_AP_vi;
////					retry_cnt_holder=&retry_cnt_AP_vi;
////					retxQ_holder=&retxQ_AP_vi;
////					retryCount=RETRY_COUNT_VI;
////					media = "VI";
////				}
//
//				ampdu_DL_currentsize.clear();
//				ampdu_DL_currentduration.clear();
//
//				APSta.dl_stas.clear();
//				for (int s=0;s<(*pacQ_holder).size();s++){
//					APSta.queuesize = (*pacQ_holder)[s].size();
//					if(APSta.queuesize>0){
//						++APSta.num_dl_STAs;
//						APSta.dl_stas.push_back(true);
//					}
//					else{
//						APSta.dl_stas.push_back(false);
//					}
////					cout << "Data in " << s << "  " << APSta.queuesize << endl;
//				}
//
//
//				if (APSta.num_dl_STAs>=4){
//					tone = RU_SIZE_242_TONES;
//				}
//				else if (APSta.num_dl_STAs>=2){
//					tone = RU_SIZE_484_TONES;
//				}
//				else if (APSta.num_dl_STAs==1){
//					tone = RU_SIZE_996_TONES;
//				}
//
////				if (APSta.num_dl_STAs==1){
////					tone=RU_SIZE_996_TONES;
////				}
////				else if(APSta.num_dl_STAs==2){
////					tone=RU_SIZE_484_TONES;
////				}
////				else if(APSta.num_dl_STAs>=3 && APSta.num_dl_STAs<=4){
////					tone=RU_SIZE_242_TONES;
////				}
////				else if(APSta.num_dl_STAs>=5 && APSta.num_dl_STAs<=8){
////					tone=RU_SIZE_106_TONES;
////				}
////				else if(APSta.num_dl_STAs>=9 && APSta.num_dl_STAs<=18){
////					tone=RU_SIZE_52_TONES;
////				}
//
//
////				cout << "#STAs with data: " << APSta.num_dl_STAs << "\ttone: " << tone << endl;
//				APSta.dl_stas_ru.clear();
//				for(int i=0;i<APSta.dl_stas.size();i++){
//					if (APSta.dl_stas[i]){
//						APSta.dl_stas_ru.push_back(tone);
//					}
//					else{
//						APSta.dl_stas_ru.push_back(0);
//					}
//				}
//				APSta.current_size.clear();
//				for (int s=0;s<(*pacQ_holder).size();s++){
//					APSta.queuesize=(*pacQ_holder)[s].size();
//					queue_size = APSta.queuesize;
//					APSta.current_size.push_back(std::min(queue_size, getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], MAX_PPDU_DURATION_US, packet_size)));
//					APSta.current_duration = getOfdmaAMpduDuration (mcs, APSta.dl_stas_ru[s], APSta.current_size[s], packet_size, bw);
////					cout << "sim_time:  " << sim_time << "\t latest size: " << APSta.current_size.back() << "\tmedia: " << media.c_str() << "\tq size " << queue_size << "\tQ non-empty?: " << APSta.dl_stas[s] <<
////							"\t OFDMA length: " << getOfdmaAMpduLength(mcs, APSta.dl_stas_ru[s], MAX_PPDU_DURATION_US, packet_size) << "\tDL RU: " << APSta.dl_stas_ru[s] << endl;
//					//APSta.index_ap = APSta.current_size.back()-1;
////					printf("  AP \t Media: %s \t AMPDU %d \t duration %d\n", media.c_str(), APSta.current_size[s], APSta.current_duration);
//
//					if(APSta.current_duration>APSta.max_duration){
//						APSta.max_duration=APSta.current_duration;
//					}
//
//					// call function to update the retry table entries
//					AC_packets = updateRetryInfo(s, APSta.current_size.back()-1, retryCount, false, sim_time);
//					APSta.dropped_ha += AC_packets.ha;
//
////					cout << "AP: " << s << "   Dropped: " << APSta.dropped_vi << " packets" << endl;
//				}
//				//APSta.current_size.clear();
//					// Short retry limit related computations
////					if ((*retry_cnt_holder)[s].empty()){
////						(*retry_cnt_holder)[s].push_back(1);
////						(*retxQ_holder)[s].push_back((*pacQ_holder)[s][APSta.index_ap]);
////					}
////
////					else {
////						// update existing entries
////						if (((*pacQ_holder)[s][APSta.index_ap]>=(*retxQ_holder)[s].back())){
////							for (int k=0;k<(*retxQ_holder)[s].size();k++){
////								(*retry_cnt_holder)[s][k] += 1;
////							}
////						}
////						// add new entries
////						if (((*pacQ_holder)[s][APSta.index_ap]>(*retxQ_holder)[s].back())){
////							(*retxQ_holder)[s].push_back((*pacQ_holder)[s][APSta.index_ap]);
////							(*retry_cnt_holder)[s].push_back(1);
////						}
////
////						// delete MPDUs if retry count threshold is exceeded
////						if ((*retry_cnt_holder)[s].front()>retryCount){
////							for(int y=0;y<(*pacQ_holder)[s].size();y++){
////								if ((*retxQ_holder)[s].front()>=(*pacQ_holder)[s][y]){
////									++APSta.count_remove_drop;
////								}
////								else{
////									break;
////								}
////							}
////
////							(*pacQ_holder)[s].erase((*pacQ_holder)[s].begin(), (*pacQ_holder)[s].begin()+APSta.count_remove_drop);
////							(*retry_cnt_holder)[s].erase((*retry_cnt_holder)[s].begin(), (*retry_cnt_holder)[s].begin()+1);
////							(*retxQ_holder)[s].erase((*retxQ_holder)[s].begin(), (*retxQ_holder)[s].begin()+1);
////							if (nSenders_ha>1){
////								APSta.dropped_ha += APSta.count_remove_drop;
////							}
////							else if ((nSenders_ha==0) && (nSenders_vi>0)){
////								APSta.dropped_vi += APSta.count_remove_drop;
////							}
////							APSta.count_remove_drop=0;
////						}
////					}
//
//
//			}




			//max_duration = (max_duration_STA>=APSta.max_duration) ? max_duration_STA : APSta.max_duration;




		//-------------------------- END OF PACKAGE 3 --------------------------//


		//-------------------------- START OF PACKAGE 4 --------------------------//

		/*** BT Update step of STAs based on the (no) collisions ***/

		//if there is no transmission, decrease BT of STAs. Otherwise, do not decrease BT but initialize invalid BT
		for (int i = 0; i < nRAStas; i++) {
			if ((nSenders_ha == 0) && (nSenders_vi==0)) {
				if (RAStas[i].bt_ha>0){
					RAStas[i].bt_ha -= 1;
				}
//				if (RAStas[i].bt_vi>0){
//					RAStas[i].bt_vi -= 1;
//				}
			}

			// virtual collision b/w HA-VI queues belonging to same STA -- HA will transmit
//			else if (((nSenders_ha==1) && (nSenders_vi==1)) && (ha_index==vi_index)){
//				// maintain CW of VI at the same value
//				RAStas[ha_index].bt_vi = rand() % (RAStas[i].cw_vi + 1);
//				RAStas[ha_index].max_bt_vi += RAStas[i].bt_vi;
//			}

			// belonging to diff STAs -- collision
			else if (((nSenders_ha==1) && (nSenders_vi==1)) && (ha_index!=vi_index)){
				if (RAStas[i].bt_ha < 0 && pacQ_STA_ha[i].size()) {
					RAStas[i].cw_ha = std::min((RAStas[i].cw_ha + 1) * 2 - 1, CW_MAX_HA);
					RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1); //100000000  for ver-2
					RAStas[i].max_bt_ha += RAStas[i].bt_ha;
				}
//				if (RAStas[i].bt_ha < 0 && pacQ_STA_ha[i].size()) {
//					RAStas[i].cw_vi = std::min((RAStas[i].cw_vi + 1) * 2 - 1, CW_MAX_VI);
//					RAStas[i].bt_vi = rand() % (RAStas[i].cw_vi + 1);
//					RAStas[i].max_bt_vi += RAStas[i].bt_vi;
//				}
			}


			// collision b/w HA sources
//			"nSenders_ha=1" to account for the cases where bt_ha=-1 but some packets are generated post DL-OFDMA and the STA didn't have opportunity for multi-TID
			else if ((nSenders_ha >= 1)) {

//				if (pacQ_STA_ha[i].empty()){
//					RAStas[i].cw_ha = CW_MIN_HA;
//					RAStas[i].bt_ha = -1;
//				}

//				if (nSenders_ha==1){
//					if ((RAStas[i].bt_ha < 0) && (pacQ_STA_ha[i].size()>0)) {
//						if (ap_wins){
//							vid_delay_file << "UL-OFDMA done, but increasing other STA: " << i << " BT from " << RAStas[i].bt_ha << " to ";
//						}
//
//						RAStas[i].cw_ha = CW_MIN_HA;
//						RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1);
//						if (nSenders_ha==1){
//							if (ap_wins){
//								vid_delay_file << RAStas[i].bt_ha << " because Q-size is: " << pacQ_STA_ha[i].size() << endl;											}
//						}
//						RAStas[i].max_bt_ha += RAStas[i].bt_ha;
//						//					printf("STA %d HA backing off to %d\n", i, RAStas[i].bt_ha);
//					}
//				}
				if (nSenders_ha==1){
					if ((RAStas[i].bt_ha < 0) && (pacQ_STA_ha[i].size()>0)) {
						if (ap_wins){
							vid_delay_file << "UL-OFDMA done, but increasing other STA: " << i << " BT from " << RAStas[i].bt_ha << " to ";
							vid_delay_file << RAStas[i].bt_ha << " because Q-size is: " << pacQ_STA_ha[i].size() << endl;
//							RAStas[i].cw_ha = int(CW_MIN_HA*0.5);
						}
					}
				}

//				else{
					//there are more than 1 sender. find them, increase their CW, and set their BT
				if ((RAStas[i].bt_ha < 0) && (pacQ_STA_ha[i].size()>0)) {
					if (RAStas[i].cw_ha==0){
//						vid_delay_file << "STA- " << i << ": Expanding CW from " << RAStas[i].cw_ha ;
						RAStas[i].cw_ha = CW_MIN_HA;
						RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1); // 100000000 for ver-2
						logging_file << sim_time << ";" << sim_time+RAStas[i].bt_ha*SLOT_TIME << ";" << "STA" << i << ";B;-" << endl;
//						vid_delay_file << " to " << RAStas[i].cw_ha <<  "  BT: " << RAStas[i].bt_ha << endl;
					}

					else{
//						vid_delay_file << "STA- " << i << ": Expanding CW from " << RAStas[i].cw_ha;
						RAStas[i].cw_ha = std::min((RAStas[i].cw_ha + 1) * 2 - 1, CW_MAX_HA);
						RAStas[i].bt_ha = rand() % (RAStas[i].cw_ha + 1); // 100000000 for ver-2
						logging_file << sim_time << ";" << sim_time+RAStas[i].bt_ha*SLOT_TIME << ";" << "STA" << i << ";B;-" << endl;

//						vid_delay_file << " to " << RAStas[i].cw_ha << "  BT: " << RAStas[i].bt_ha << endl;
					}

//					vid_delay_file << "adjusting CW -- Q-size of STA-" << i << ": " << RAStas[i].cw_ha << endl;
					RAStas[i].max_bt_ha += RAStas[i].bt_ha;
					//					printf("STA %d HA backing off to %d\n", i, RAStas[i].bt_ha);
				}


//				}


				// virtual collision HA-VI sources
//				if (nSenders_vi>=1){
//					if (RAStas[i].bt_vi < 0 && pacQ_STA_vi[i].size()) {
//						if (RAStas[i].bt_ha < 0 && pacQ_STA_vi[i].size()){
//							RAStas[i].bt_vi = rand() % (RAStas[i].cw_vi + 1);
//							RAStas[ha_index].max_bt_vi += RAStas[i].bt_vi;
//						}
//						else{
//							RAStas[i].cw_vi = std::min((RAStas[i].cw_vi + 1) * 2 - 1, CW_MAX_VI);
//							RAStas[i].bt_vi = rand() % (RAStas[i].cw_vi + 1);
//							RAStas[i].max_bt_vi += RAStas[i].bt_vi;
//						}
//					}
//
//				}
			}

			// collision b/w VI sources
//			else if ((nSenders_vi > 1)) {
//				//there are more than 1 sender. find them, increase their CW, and set their BT
//				if (RAStas[i].bt_vi < 0 && pacQ_STA_vi[i].size()) {
//					RAStas[i].cw_vi = std::min((RAStas[i].cw_vi + 1) * 2 - 1, CW_MAX_VI);
//					RAStas[i].bt_vi = rand() % (RAStas[i].cw_vi + 1);
//					RAStas[i].max_bt_vi += RAStas[i].bt_vi;
////					printf("3 --- STA %d   VI queue size %d   backing off to %d\n", i, pacQ_STA_vi[i].size(), RAStas[i].bt_vi);
////
////					if (i==0){
////						staO_file << "sim_time: " << sim_time << " --- backing off to " << RAStas[i].bt_vi <<  endl;
////						cout << "sim_time: " << sim_time << " --- backing off to " << RAStas[i].bt_vi <<  endl;
////
////					}
//				}
//			}



		}

		//-------------------------- END OF PACKAGE 4 --------------------------//

		//-------------------------- START OF PACKAGE 5 --------------------------//

		/*** BT Update step of APs based on the (no) collisions ***/

		//if there is no transmission, decrease BT of AP. Otherwise, do not decrease BT but initialize BT if invalid
		//the AP contends for the channel in the following cases: UL_OFDMA_WITH_EDCA, DL_OFDMA_WITH_EDCA, DL_MU_MIMO_WITH_EDCA
		//the AP does not contend for the channel in PURE_EDCA (we consider that only the STAs contends) and in PURE_UL_OFDMA

		if ((nSenders_ha == 0) && (nSenders_vi==0)) {
			if (APSta.bt_ha>0){
				APSta.bt_ha -= 1;
			}
		}

		else if ((nSenders_ha > 1)) {
			//there are more than 1 sender. find them, increase their CW, and set their BT
			if (APSta.bt_ha < 0 && ap_wins) {
				if (APSta.cw_ha==0){
					APSta.cw_ha = CW_MIN_HA;
					APSta.bt_ha = rand() % (APSta.cw_ha + 1);
					logging_file << sim_time << ";" << sim_time+APSta.bt_ha*SLOT_TIME << ";AP;B;-" << endl;

//					vid_delay_file << "AP:     Expanding CW from 0 to " << APSta.cw_ha << "  BT: " << APSta.bt_ha << endl;
				}
				else{
//					vid_delay_file << "AP:     Expanding CW from " << APSta.cw_ha;
					APSta.cw_ha = std::min((APSta.cw_ha + 1) * 2 - 1, CW_MAX_HA);
					APSta.bt_ha = rand() % (APSta.cw_ha + 1);
					logging_file << sim_time << ";" << sim_time+APSta.bt_ha*SLOT_TIME << ";AP;B;-" << endl;
//					vid_delay_file << " to " << APSta.cw_ha << "  BT: " << APSta.bt_ha << endl;
				}
				vid_delay_file << "\n" << endl;

				APSta.max_bt_ha += APSta.bt_ha;
				sta_file << "adjusting CW -- Q-size of AP: " << APSta.cw_ha << endl;
//				printf("AP HA backing off to %d\n", APSta.bt_ha);
			}

		}

		//-------------------------- END OF PACKAGE 5 --------------------------//
	}


	//-------------------------- START OF PACKAGE 6 --------------------------//

	struct wlan_result result;

	double collision_rate = 0;
	if ((nCollisions + nNoCollisions) > 0){
		collision_rate = nCollisions * 100.0 / (nCollisions + nNoCollisions);
	}

#if 0
	//print some results
	printf("EDCA :\n");
	printf("EDCA A-MPDU length : %d\n", edca_ampdu_len);
	printf("EDCA A-MPDU duration : %dus\n", edca_ampdu_duration);
	printf("Number of EDCA MPDUs : %d\n", nTx);
	printf("Number of successful EDCA transmissions (number of A-MPDUs) : %d\n", nNoCollisions);
	printf("Number of EDCA collisions : %d\n", nCollisions);
	printf("EDCA collision rate : %.2f%%\n", collision_rate);
#endif

	//result.edca_ampdu_len = edca_ampdu_len;
	//result.edca_ampdu_duration = edca_ampdu_duration;
	result.edca_n_tx_mpdu = nTx;
	result.edca_nNoCollisions = nNoCollisions;
	result.edca_nCollisions = nCollisions;
	result.edca_collision_rate = collision_rate;

	collision_rate = 0;

	if ((ofdma_stats.nCollisions + ofdma_stats.nNoCollisions) > 0){
		collision_rate = ofdma_stats.nCollisions * 100.0 / (ofdma_stats.nCollisions + ofdma_stats.nNoCollisions);
	}
	printf("%d \t %d \t %d", AP_Tx_count, UL_Tx_count, RAStas[0].nTx);
//	double throughput = AP_Tx_count + UL_Tx_count; //WLAN throughput, i.e. EDCA + UL OFDMA throughput
	throughput = throughput * 1000 * 8 / MAX_SIMULATION_TIME_US;

#if 0
	printf("\n\nOFDMA :\n");
	printf("OFDMA A-MPDU length : %d\n", ofdma_ampdu_len);
	printf("Number of SA transmitted MPDUs : %d\n", ofdma_stats.nSATx);
	printf("Number of successful RA transmitted MPDUs : %d\n", ofdma_stats.nRATx);

	printf("Number of collisions on RA RUs    : %d\n", ofdma_stats.nCollisions);
	printf("Number of no collisions on RA RUs : %d\n", ofdma_stats.nNoCollisions);

	printf("Collision rate : %.2f%%\n", collision_rate);

	printf("\n\nWLAN throughput : %.2f Mbps\n", throughput);
#endif

	//result.ofdma_ampdu_len = ofdma_ampdu_len;
	result.ofdma_n_SA_tx_mpdus = ofdma_stats.nSATx;
	result.ofdma_n_RA_tx_mpdus = ofdma_stats.nRATx;
	result.ofdma_nNoCollisions = ofdma_stats.nCollisions;
	result.ofdma_nCollisions = ofdma_stats.nNoCollisions;
	result.ofdma_collision_rate = collision_rate;

	result.throughput = throughput;

	//record the average tx delays
	//average transmission delays of AP is valid only in cases of DL OFDMA and DL MU-MIMO
	result.avgApTxDelaysMicros = 0;
//	if (APSta.nSuccAccesses > 0) {
//
//
//		result.avgApTxDelaysMicros = APSta.sumDelays / APSta.nSuccAccesses;
//	}
//
//	//average transmission delays of RA STAs (the average of one STA is enough)
//	result.avgRAStasTxDelaysMicros = 0;
//	if (nRAStas > 0 && RAStas[0].nSuccAccesses > 0) {
//		result.avgRAStasTxDelaysMicros = RAStas[0].sumDelays / RAStas[0].nSuccAccesses;
//	}
	float delaytotalglobal=0;
	int samplesglobal=0, numaccess_mu=0, numaccess_su=0;
	float sumsqdiff=0, sumsqdiffglo=0;
	float averg;
	vector <int> delays_allSta, ampdu_allSta;
	long int STA_generated_ha = 0, STA_dropped_ha = 0, AP_generated_ha = 0, AP_dropped_ha = 0,
			STA_generated_vi = 0, STA_dropped_vi = 0, AP_generated_vi = 0, AP_dropped_vi = 0;
	ofstream file;
	string temp;


	printf("\n\n *************** STA Haptic packet statistics ***************\n");

	for (int i=0;i<nRAStas;i++){
		int samples = RAStas[i].delaysList.HA.size();
//		printf("\n total samples: %d\n",samples);

		float averg = accumulate(RAStas[i].delaysList.HA.begin(), RAStas[i].delaysList.HA.end(), 0.0)*1.0/(samples*1000);
		delaytotalglobal += averg*samples;
		samplesglobal += samples;

		for (int j=0; j<samples; j++){
//			printf("avg: %d\n",averg);
//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
			sumsqdiff += (RAStas[i].delaysList.HA[j]/1000.0-averg)*(RAStas[i].delaysList.HA[j]/1000.0-averg);
			delay_file_STA_HA << RAStas[i].delaysList.HA[j] << "\n" ;

		}
		//printf("STA %d \t avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f #access: %d \n",i, averg, sumsqdiff, sqrt(sumsqdiff*1.0/samples), RAStas[i].nSuccAccess_HA);
		numaccess +=  RAStas[i].nSuccAccess_HA;
		numaccess_mu += RAStas[i].nSuccAccess_mu_HA;
		numaccess_su += RAStas[i].nSuccAccess_su_HA;

		printf ("STA %d \t generated %d \t dropped %d \t dropped (%) %f\n", i, RAStas[i].generated_ha, RAStas[i].dropped_ha, RAStas[i].dropped_ha*100.0/RAStas[i].generated_ha);
		copy(RAStas[i].delaysList.HA.begin(), RAStas[i].delaysList.HA.end(), back_inserter(delays_allSta));

		STA_generated_ha += RAStas[i].generated_ha;
		STA_dropped_ha += RAStas[i].dropped_ha;
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	//	printf( "\n All delays mean:  %f \n", averg);

	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

//	float ft_fraction = FRAGMENT_THRESHOLD*FRAGMENT_SIZE*1.0/PACKET_SIZE_BWD_VI;
	temp = std::string("./ResultsFiles/Latency/Haptic/") + "STA-" + std::to_string(nRAStas)
						+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + "-B-" + std::to_string(buffer_limit)
						+ std::string(".txt");
	file.open(temp);
	for (const auto &e : delays_allSta)
		file << e*1.0/1000.0 << "\n";

	file.close();

	//printf ("\nGlobal avg. delay: %f", delaytotalglobal*1.0/samplesglobal);
	printf("\nGlobal avg delay w. jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));
	global_buffer << buffer_limit << "\t" << nRAStas << "\t" << averg << "\t" << STA_dropped_ha*100.0/STA_generated_ha << "\t";
	frag_thresh_file << fragment_threshold << "\t" << buffer_limit << "\t" << nRAStas << "\t" << averg << "\t" << STA_dropped_ha*100.0/STA_generated_ha << "\t";
	delaytotalglobal=0;
	samplesglobal=0;
	numaccess_mu=0;
	numaccess_su=0;
	sumsqdiff=0;
	sumsqdiffglo=0;
	averg=0;
	delays_allSta.clear();
	ampdu_allSta.clear();

	for (int i=0;i<nRAStas;i++){
		int samples = RAStas[i].sampleAccessDelay.size();
//		printf("\n total samples: %d\n",samples);

		float averg = accumulate(RAStas[i].sampleAccessDelay.begin(), RAStas[i].sampleAccessDelay.end(), 0.0)*1.0/(samples*1000);
		delaytotalglobal += averg*samples;
		samplesglobal += samples;

		for (int j=0; j<samples; j++){
			//			printf("avg: %d\n",averg);
			//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
			sumsqdiff += (RAStas[i].sampleAccessDelay[j]/1000.0-averg)*(RAStas[i].sampleAccessDelay[j]/1000.0-averg);
			delay_file_STA_HA << RAStas[i].sampleAccessDelay[j] << "\n" ;

		}
		//printf("STA %d \t avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f #access: %d \n",i, averg, sumsqdiff, sqrt(sumsqdiff*1.0/samples), RAStas[i].nSuccAccess_HA);

		copy(RAStas[i].sampleAccessDelay.begin(), RAStas[i].sampleAccessDelay.end(), back_inserter(delays_allSta));
		copy(RAStas[i].ampduLength_ha.begin(), RAStas[i].ampduLength_ha.end(), back_inserter(ampdu_allSta));
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	//	printf( "\n All delays mean:  %f \n", averg);

	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}


	printf("\nGlobal avg delay without jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));


	printf("Delay right after UL-OFDMA (ms): %f \n\n", accumulate(ulofdmadelay_sta.begin(), ulofdmadelay_sta.end(), 0.0)*1.0/(ulofdmadelay_sta.size()*1000));
	printf("Delay apart from above (ms): %f \n\n", accumulate(nonulofdmadelay_sta.begin(), nonulofdmadelay_sta.end(), 0.0)*1.0/(nonulofdmadelay_sta.size()*1000));
	printf("Delay other (ms): %f \n\n", accumulate(otherdelay.begin(), otherdelay.end(), 0.0)*1.0/(otherdelay.size()*1000));

	printf("Total: %d \t right after OFDMA: %d \t non-OFDMA: %d", delays_allSta.size(), ulofdmadelay_sta.size(),
			nonulofdmadelay_sta.size());

	printf("\n\n----------------- AMPDU size -----------------\n");
	printf("Global: %lld \t #Access: %d \t avg. : %f", ampdu_sta_mu_HA+ampdu_sta_su_HA, numaccess,
			(ampdu_sta_mu_HA+ampdu_sta_su_HA)*1.0/numaccess);

//	PACKET_SIZE_BWD_HA << "\t" << PACKET_SIZE_BWD_VI << "\t" << PACKET_SIZE_FWD_HA << "\t" <<
	global_file << nRAStas << "\t"
			<< averg << "\t" << sqrt(sumsqdiffglo*1.0/delays_allSta.size()) << "\t" <<  STA_dropped_ha*100.0/STA_generated_ha << "\t" ;
	hap_delay_p_file << averg << ", " ;
	// accumulate(STA_HA_queuesize.begin(), STA_HA_queuesize.end(), 0)*1.0/(STA_HA_queuesize.size()) << "\t"


	temp = std::string("./ResultsFiles/Latency/Haptic/") + "STA-" + std::to_string(nRAStas)
			+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + std::string(".txt");
	file.open(temp);
    for (const auto &e : delays_allSta)
    	file << e*1.0/1000.0 << "\n";

    file.close();

	printf("\n\n----------------- SU-OFDMA -----------------\n");

	delays_allSta.clear();
	for (int i=0;i<nRAStas;i++){
		copy(RAStas[i].delays_su.HA.begin(), RAStas[i].delays_su.HA.end(), back_inserter(delays_allSta));
	}
	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);

	sumsqdiffglo=0;
	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

	printf("\n----- avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));

	printf("STA: Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", ampdu_sta_su_HA+ampdu_sta_su_HA, numaccess_su,
			(ampdu_sta_su_HA+ampdu_sta_su_HA)*1.0/numaccess_su);

	printf("\n\n----------------- MU-OFDMA -----------------\n");

	delays_allSta.clear();
	for (int i=0;i<nRAStas;i++){
		copy(RAStas[i].delays_mu.HA.begin(), RAStas[i].delays_mu.HA.end(), back_inserter(delays_allSta));
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	sumsqdiffglo=0;
	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

	printf("\n ----- avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));

	printf("STA: Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", ampdu_sta_mu_HA+ampdu_sta_mu_HA, numaccess_mu,
				(ampdu_sta_mu_HA+ampdu_sta_mu_HA)*1.0/numaccess_mu);


	delaytotalglobal=0;
	samplesglobal=0;
	numaccess_mu=0;
	numaccess_su=0;
	sumsqdiff=0;
	sumsqdiffglo=0;
	averg=0;
	delays_allSta.clear();



	printf("\n\n *************** STA Video packet statistics ***************\n");

	for (int i=0;i<nRAStas;i++){
		int samples = RAStas[i].sampleAccessDelayVid.size();
//		printf("\n total samples: %d\n",samples);

		float averg = accumulate(RAStas[i].sampleAccessDelayVid.begin(), RAStas[i].sampleAccessDelayVid.end(), 0.0)*1.0/(samples*1000);
		delaytotalglobal += averg*samples;
		samplesglobal += samples;

		for (int j=0; j<samples; j++){
			//			printf("avg: %d\n",averg);
			//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
			sumsqdiff += (RAStas[i].sampleAccessDelayVid[j]/1000.0-averg)*(RAStas[i].sampleAccessDelayVid[j]/1000.0-averg);
			delay_file_STA_VI << RAStas[i].sampleAccessDelayVid[j] << "\n" ;

		}
		//printf("STA %d \t avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f #access: %d \n",i, averg, sumsqdiff, sqrt(sumsqdiff*1.0/samples), RAStas[i].nSuccAccess_HA);
		numaccess +=  RAStas[i].nSuccAccess_VI;
		numaccess_mu += RAStas[i].nSuccAccess_mu_VI;
		numaccess_su += RAStas[i].nSuccAccess_su_VI;

		printf ("STA %d \t generated %d \t dropped %d \t dropped (%) %f\n", i, RAStas[i].generated_vi, RAStas[i].dropped_vi, RAStas[i].dropped_vi*100.0/RAStas[i].generated_vi);
		copy(RAStas[i].sampleAccessDelayVid.begin(), RAStas[i].sampleAccessDelayVid.end(), back_inserter(delays_allSta));

		STA_generated_vi += RAStas[i].generated_vi;
		STA_dropped_vi += RAStas[i].dropped_vi;
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	//	printf( "\n All delays mean:  %f \n", averg);

	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

	global_file << averg << "\t" << sqrt(sumsqdiffglo*1.0/delays_allSta.size()) << "\t" <<  STA_dropped_vi*100.0/STA_generated_vi << "\t";
	global_buffer << averg << "\t" << STA_dropped_vi*100.0/STA_generated_vi << "\t";
	frag_thresh_file << averg << "\t" << STA_dropped_vi*100.0/STA_generated_vi << "\t";

	vid_delay_p_file << averg << ", ";

	//	printf ("\nGlobal avg. delay: %f", delaytotalglobal*1.0/samplesglobal);
	printf("\nGlobal avg delay without jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));


	temp = std::string("./ResultsFiles/Latency/Video/") + "STA-" + std::to_string(nRAStas)
					+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + "-B-" + std::to_string(buffer_limit)  + std::string(".txt");
	file.open(temp);
	for (const auto &e : delays_allSta)
		file << e*1.0/1000.0 << "\n";
	file.close();

	delaytotalglobal=0;
	samplesglobal=0;
	numaccess_mu=0;
	numaccess_su=0;
	sumsqdiff=0;
	sumsqdiffglo=0;
	averg=0;
	delays_allSta.clear();

	for (int i=0;i<nRAStas;i++){
		int samples = RAStas[i].delaysList.VI.size();
//		printf("\n total samples: %d\n",samples);

		float averg = accumulate(RAStas[i].delaysList.VI.begin(), RAStas[i].delaysList.VI.end(), 0.0)*1.0/(samples*1000);
		delaytotalglobal += averg*samples;
		samplesglobal += samples;

		for (int j=0; j<samples; j++){
			//			printf("avg: %d\n",averg);
			//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
			sumsqdiff += (RAStas[i].delaysList.VI[j]/1000.0-averg)*(RAStas[i].delaysList.VI[j]/1000.0-averg);
			delay_file_STA_VI << RAStas[i].delaysList.VI[j] << "\n" ;

		}

		copy(RAStas[i].delaysList.VI.begin(), RAStas[i].delaysList.VI.end(), back_inserter(delays_allSta));
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	//	printf( "\n All delays mean:  %f \n", averg);

	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}


	printf("\nGlobal avg delay with jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));

	printf("\n\n----------------- AMPDU size -----------------\n");
	printf("Global: %lld \t #Access: %d \t avg. : %f", ampdu_sta_mu_VI+ampdu_sta_su_VI, numaccess,
			(ampdu_sta_mu_VI+ampdu_sta_su_VI)*1.0/numaccess);

//	temp = std::string("/home/vineet/Documents/Git-Fresh/DQ-full-OFDMAsingle/ResultsFiles/Video/STA-") + std::to_string(nRAStas)
//		+ "-" + std::to_string(PACKET_SIZE_BWD_VI) + std::string(".txt");
//	file.open(temp);
//	for (const auto &e : delays_allSta)
//		file << e*1.0/1000.0 << "\n";
//	file.close();

	printf("\n\n----------------- SU-OFDMA -----------------\n");

	delays_allSta.clear();
	for (int i=0;i<nRAStas;i++){
		copy(RAStas[i].delays_su.VI.begin(), RAStas[i].delays_su.VI.end(), back_inserter(delays_allSta));
	}
	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);

	sumsqdiffglo=0;
	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

	printf("\n----- avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));

	printf("STA: Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", ampdu_sta_su_VI+ampdu_sta_su_VI, numaccess_su,
			(ampdu_sta_su_VI+ampdu_sta_su_VI)*1.0/numaccess_su);

	printf("\n\n----------------- MU-OFDMA -----------------\n");

	delays_allSta.clear();
	for (int i=0;i<nRAStas;i++){
		copy(RAStas[i].delays_mu.VI.begin(), RAStas[i].delays_mu.VI.end(), back_inserter(delays_allSta));
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	sumsqdiffglo=0;
	for (int j=0; j<delays_allSta.size(); j++){
		sumsqdiffglo += (delays_allSta[j]/1000.0-averg)*(delays_allSta[j]/1000.0-averg);
	}

	printf("\n ----- avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delays_allSta.size()));

	printf("STA: Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", ampdu_sta_mu_VI+ampdu_sta_mu_VI, numaccess_mu,
			(ampdu_sta_mu_VI+ampdu_sta_mu_VI)*1.0/numaccess_mu);


	printf("\n\nVideo samples transmitted: Total: %d \t OFDMA: %d\t EDCA: %d ", STA_generated_vi, vi_ofdma_count, vi_edca_count);

	printf("\n\nTotal collisions: %d \t Video collisions: %d \t \% video collisions: %f", numCollisions, numVidCollisions,
			numVidCollisions*1.0/numCollisions);

	vid_metadata_file << nRAStas << "\t" << vi_ofdma_count << "\t" << vi_edca_count << "\t" <<
			vi_ofdma_count*100.0/(vi_ofdma_count+vi_edca_count) << "\t" << numCollisions << "\t" << numVidCollisions << "\t" <<
			numVidCollisions*100.0/numCollisions << endl;

	delaytotalglobal=0;
	samplesglobal=0;
	numaccess_mu=0;
	numaccess_su=0;
	sumsqdiff=0;
	sumsqdiffglo=0;
	averg=0;
	delays_allSta.clear();


//	printf("\n\n *************** STA Video packet statistics ***************\n");
//
//	averg = accumulate(delay_vid.begin(), delay_vid.end(), 0.0)*1.0/(delay_vid.size());
//	for (int j=0; j<delay_vid.size(); j++){
//		sumsqdiffglo += (delay_vid[j]-averg)*(delay_vid[j]-averg);
//	}
//
//	printf("\n ----- avg delay (ms): %f \t sumdiff %f \t stddev (ms): %f \n", averg,sumsqdiffglo,sqrt(sumsqdiffglo*1.0/delay_vid.size()));
//
//
//	delaytotalglobal=0;
//	samplesglobal=0;
//	numaccess_mu=0;
//	numaccess_su=0;
//	sumsqdiff=0;
//	sumsqdiffglo=0;
//	averg=0;
//	delays_allSta.clear();

	printf("\n\n *************** AP Haptic packet statistics ***************\n");

	float APdelavg = accumulate(APSta.delaysList.HA.begin(), APSta.delaysList.HA.end(), 0.0)*1.0/(APSta.delaysList.HA.size()*1000);
	float sumsqdiffap=0;
	for (int j=0; j<APSta.delaysList.HA.size(); j++){
		//			printf("avg: %d\n",averg);
		//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
		sumsqdiffap += (APSta.delaysList.HA[j]/1000.0-APdelavg)*(APSta.delaysList.HA[j]/1000.0-APdelavg);
		delay_file_AP_HA << APSta.delaysList.HA[j] << "\n";

	}
	//printf("\n total samples: %d\n",APSta.delays.size());

	samplesglobal += APSta.delaysList.HA.size();
	delaytotalglobal = (delaytotalglobal + APdelavg*APSta.delaysList.HA.size())*1.0/samplesglobal;

//	printf ("\nAP : \t generated %d \t dropped %d \t dropped (%) %f\n",  APSta.generated_ha, APSta.dropped_ha, APSta.dropped_ha*100.0/APSta.generated_ha);


	printf("\n\n-----------------Global Delay -----------------\n");

	printf("\navg delay with jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", APdelavg,sumsqdiffap,sqrt(sumsqdiffap*1.0/APSta.delaysList.HA.size()));
	global_buffer << APdelavg << "\t";
	frag_thresh_file << APdelavg << "\t";


	temp = std::string("./ResultsFiles/Latency/Kinematic/") + "STA-" + std::to_string(nRAStas)
						+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + "-B-" + std::to_string(buffer_limit) + std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.delaysList.HA)
		file << e*1.0/1000.0 << "\n";
	file.close();

	delaytotalglobal=0;
	samplesglobal=0;
	numaccess_mu=0;
	numaccess_su=0;
	sumsqdiff=0;
	sumsqdiffglo=0;
	averg=0;
	delays_allSta.clear();


	APdelavg = accumulate(APSta.sampleAccessDelay.begin(), APSta.sampleAccessDelay.end(), 0.0)*1.0/(APSta.sampleAccessDelay.size()*1000);
	sumsqdiffap=0;
	for (int j=0; j<APSta.sampleAccessDelay.size(); j++){
		//			printf("avg: %d\n",averg);
		//			printf("sample %d\t avg %f\t diff %f\n",RAStas[i].delays[j],averg,RAStas[i].delays[j]-averg);
		sumsqdiffap += (APSta.sampleAccessDelay[j]/1000.0-APdelavg)*(APSta.sampleAccessDelay[j]/1000.0-APdelavg);
		delay_file_AP_HA << APSta.sampleAccessDelay[j] << "\n";

	}
	//printf("\n total samples: %d\n",APSta.delays.size());

	samplesglobal += APSta.sampleAccessDelay.size();
	delaytotalglobal = (delaytotalglobal + APdelavg*APSta.sampleAccessDelay.size())*1.0/samplesglobal;


	printf("\n\n-----------------Global Delay -----------------\n");

	printf("\navg delay without jitter buffer (ms): %f \t sumdiff %f \t stddev (ms): %f \n", APdelavg,sumsqdiffap,sqrt(sumsqdiffap*1.0/APSta.sampleAccessDelay.size()));



	printf("Delay right after UL-OFDMA (ms): %f \n\n", accumulate(ulofdmadelay_ap.begin(), ulofdmadelay_ap.end(), 0.0)*1.0/(ulofdmadelay_ap.size()*1000));
	printf("Delay right after UL-OFDMA (ms): %f \n\n", accumulate(nonulofdmadelay_ap.begin(), nonulofdmadelay_ap.end(), 0.0)*1.0/(nonulofdmadelay_ap.size()*1000));


	printf("Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", ampdu_ap_HA, APSta.nSuccAccess_HA, ampdu_ap_HA*1.0/(APSta.nSuccAccess_HA));

	global_file << APdelavg << "\t" << sqrt(sumsqdiffap*1.0/APSta.sampleAccessDelay.size()) << "\t" <<  APSta.dropped_ha*100.0/APSta.generated_ha << "\tDL-OFDMA dur: " <<
			accumulate(dlofdma_duration.begin(), dlofdma_duration.end(), 0.0)*1.0/(dlofdma_duration.size()*1000) << "\tUL-OFDMA dur: " <<
			accumulate(ul_ofdma_dur.begin(), ul_ofdma_dur.end(), 0.0)*1.0/(ul_ofdma_dur.size()*1000) << "\tData: " <<
			"\tSignalOverhead (ms): " << time_overhead*1.0/1000 << "\t#RTS-CTS non-collision: " << rts_cts_count_noCollision << "\tOVerheadCollision: " << overhead_collision
			<< "\t#Collisions: " << numCollisions << "\tEDCA-access: " << edca_access << "\tUL-OFDMA-access: " << ul_ofdma_access << "\tDL-OFDMA-access: " << dl_ofdma_access << "\n";
//			<< "\t#AP-access: " << ap_access_counter << "\tVidEmpty: " << vi_empty_counter << "\tHA in UL-OFDMA: " << ha_ulofdma_episode << "\tVI in UL-OFDMA: " <<
//			vi_ulofdma_episode << "\n";
//	<< accumulate(AP_queuesize.begin(), AP_queuesize.end(), 0)*1.0/(AP_queuesize.size())
	global_buffer << APSta.dropped_ha*100.0/APSta.generated_ha << endl;
	frag_thresh_file << APSta.dropped_ha*100.0/APSta.generated_ha << endl;

	kin_delay_p_file << APdelavg << ", " ;

	temp = std::string("./ResultsFiles/Latency/Kinematic/") + "STA-" + std::to_string(nRAStas)
					+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.sampleAccessDelay)
		file << e*1.0/1000.0 << "\n";
	file.close();



	temp = std::string("./ResultsFiles/AMPDU/Kinematic/") + "STA-" + std::to_string(nRAStas)
							+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.ampduLength_kin)
		file << e << "\n";

	file.close();

	temp = std::string("./ResultsFiles/AMPDU/Haptic/") + "STA-" + std::to_string(nRAStas)
							+ ":FT-" + std::to_string(fragment_threshold).substr(0, 4) + std::string(".txt");
	file.open(temp);
	for (const auto &e : ampdu_allSta)
		file << e << "\n";

	file.close();


	temp = std::string("./ResultsFiles/Latency/Global/") + "AP-interarrival" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.interAccess)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "AP-interarrival-vid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.interAccess_ha_vid)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "AP-interarrival-novid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : APSta.interAccess_ha)
		file << e << "\n";
	file.close();

//	temp = std::string("/home/vineetgokhale/Documents/Git-Fresh/DQ-dummy/ResultsFiles/") + "STA-interarrival" +
//			std::string(".txt");
//	file.open(temp);
//	for (const auto &e : RAStas[0].interAccess_ha)
//		file << e << "\n";
//	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "STA-interarrival" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : sta_interAccess_ha)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "STA-interarrival-MU-vid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : sta_interAccess_mu_ha_vid)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "STA-interarrival-MU-novid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : sta_interAccess_mu_ha)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "STA-interarrival-SU-vid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : sta_interAccess_su_ha_vid)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Latency/Global/") + "STA-interarrival-SU-novid" +
			std::string(".txt");
	file.open(temp);
	for (const auto &e : sta_interAccess_su_ha)
		file << e << "\n";
	file.close();



//	temp = std::string("/home/vineetgokhale/Documents/Git-Fresh/DQ-dummy/ResultsFiles/") + "collision-1.txt";
//	file.open(temp);
//	for (const auto &e : access_collision_1)
//		file << e << "\n";
//	file.close();
//
//	temp = std::string("/home/vineetgokhale/Documents/Git-Fresh/DQ-dummy/ResultsFiles/") + "collision-2.txt";
//	file.open(temp);
//	for (const auto &e : access_collision_2)
//		file << e << "\n";
//	file.close();
//
//	temp = std::string("/home/vineetgokhale/Documents/Git-Fresh/DQ-dummy/ResultsFiles/") + "collision-3.txt";
//	file.open(temp);
//	for (const auto &e : access_collision_3)
//		file << e << "\n";
//	file.close();




	// ********************* Need to add for each AC & device
	// 1. Inter-access sim_time for each
	// 2. Buffer sim_time
	printf("\n\n *******************************************\n");
//	printf("\nAP: Total AMPDU: %lld \t #Access: %d \t Avg. AMPDU length: %f", APSta.nTx, APSta.nSuccAccesses, APSta.nTx*1.0/(APSta.nSuccAccesses*nRAStas));



//
////	printf("********* UL-OFDMA avg. max. duration: %f ********* \n", sum_dur*1.0/ul_ofdma_count*1000.0);
//
	printf("\n----------------- Average haptic inter-access sim_time -----------------\n");
	for (int i=0;i<nRAStas;i++){

		printf ("STA %d %f\n", i, accumulate(RAStas[i].accessTimeVec_ha.begin(), RAStas[i].accessTimeVec_ha.end(), 0)*1.0/(RAStas[i].accessTimeVec_ha.size()*1000.0));
	}
//
	printf ("\nAP  %f", accumulate(APSta.interAccess.begin(), APSta.interAccess.end(), 0)*1.0/(APSta.interAccess.size()*1000.0));

	delays_allSta.clear();
	for (int i=0;i<nRAStas;i++){
		copy(AP_interAccess[i].begin(), AP_interAccess[i].end(), back_inserter(delays_allSta));
	}

	averg = accumulate(delays_allSta.begin(), delays_allSta.end(), 0.0)*1.0/(delays_allSta.size()*1000);
	printf ("\nAP Q-wise %f", averg);

	averg=0;

	averg = accumulate(APSta.accessdelay.begin(), APSta.accessdelay.end(), 0.0)*1.0/(APSta.accessdelay.size()*1000);
	printf ("\nAP Q-wise new %f  length %d", averg, APSta.accessdelay.size());

	averg=0;


	printf("\n----------------- Average video inter-access sim_time -----------------\n");
	for (int i=0;i<nRAStas;i++){

		printf ("STA %d %f\n", i, accumulate(RAStas[i].accessTimeVec_vi.begin(), RAStas[i].accessTimeVec_vi.end(), 0)*1.0/(RAStas[i].accessTimeVec_vi.size()*1000.0));
	}
//

	printf ("\nGlobal avg. delay: %f", delaytotalglobal*1.0/samplesglobal);
//
//
//	printf("\n\n ----------------- Average buffer size -----------------\n");
//	printf("STA: %f \t AP: %f\n",
//			buffer_size_sta*1.0/buffer_size_sta_count, buffer_size_ap*1.0/buffer_size_ap_count);
////	std::ofstream output_file("./APdelays.txt");
////	//std::ostream_iterator<std::int> output_iterator(output_file, "\n");
////	std::copy(APSta.delays.rbegin(), APSta.delays.rend(), std::ostream_iterator<int>(output_file, "\n"));
//	//std::copy(APSta.delays.begin(), APSta.delays.end(), output_iterator);
//
//	printf("\n\n ----------------- Back off timer ----------------- \n\n AP: %ld \t STA: %d \t%f", ap_maxbt, APSta.nSuccAccesses, ap_maxbt*1.0/APSta.nSuccAccesses);
//
//
//	printf("\n\n ----------------- Video packet statistics -----------------\n");
//	for (int i=0;i<nRAStas;i++){
//		printf ("STA %d \t generated %d \t dropped %d \t dropped (%) %f\n", i, RAStas[i].generated_vi, RAStas[i].dropped_vi, RAStas[i].dropped_vi*100.0/RAStas[i].generated_vi);
//	}
//	printf ("\nAP : \t generated %d \t dropped %d \t dropped (%) %f\n",  APSta.generated_vi, APSta.dropped_vi, APSta.dropped_vi*100.0/APSta.generated_vi);
//
//
//	printf("\n\n AP Tx. sim_time: %f", accumulate(txtime_ap.begin(), txtime_ap.end(), 0)*1.0/(txtime_ap.size()*1000.0));
//	printf("\n STA Tx. sim_time: %f", accumulate(txtime_sta.begin(), txtime_sta.end(), 0)*1.0/(txtime_sta.size()*1000.0));
//
//
//	printf("\n\n STA 0 AMPDU total: \t UL-OFDMA: %lld \t UL-EDCA: %lld \t DL-OFDMA: %lld", ul_zero_ofdma_ampdu, ul_zero_edca_ampdu, dl_zero_ofdma_ampdu);
//
//	printf("\n\n STA 0 AMPDU avg. size: \t UL-OFDMA: %f \t UL-EDCA: %f \t DL-OFDMA: %f", ul_zero_ofdma_ampdu*1.0/ul_zero_ofdma_access,
//			ul_zero_edca_ampdu*1.0/ul_zero_edca_access, dl_zero_ofdma_ampdu*1.0/dl_zero_ofdma_access);
//
//	printf("\n\n STA 0 delay: \t UL-OFDMA: %f \t UL-EDCA: %f \t DL-OFDMA: %f",
//			accumulate(ul_zero_ofdma_delay.begin(), ul_zero_ofdma_delay.end(), 0.0)*1.0/(ul_zero_ofdma_delay.size()*1000),
//			accumulate(ul_zero_edca_delay.begin(), ul_zero_edca_delay.end(), 0.0)*1.0/(ul_zero_edca_delay.size()*1000),
//			accumulate(dl_zero_ofdma_delay.begin(), dl_zero_ofdma_delay.end(), 0.0)*1.0/(dl_zero_ofdma_delay.size()*1000));
//
//
//	printf("\n\n Total DL-OFDMA duration (ms): %lld \t Total DL-OFDMA frames: %lld \t sim_time/frame: %f", dl_ofdma_tot_dur, dl_ofdma_tot_frame,
//			dl_ofdma_tot_dur*1.0/(dl_ofdma_tot_frame*1000));
//
//	printf("\n\n Total UL-OFDMA duration: %lld \t Total UL-OFDMA frames: %lld \t sim_time/frame: %f", ul_ofdma_tot_dur, ul_ofdma_tot_frame,
//				ul_ofdma_tot_dur*1.0/(ul_ofdma_tot_frame*1000));

	time_track << nRAStas << "\t" << "Send: " << APSta.time_send/1000.0 <<  "\tDataSend: " << APSta.time_dataSend/1000.0 << "\tOFDMAframe: " << dl_ofdma_tot_frame <<
			"\tCollision: " << APSta.time_collision/1000.0 << "\t" << "Idle: " << APSta.time_idle/1000.0 << "\t" << "Sta-send: " << APSta.time_staSend/1000.0 <<
			"\tSta-Datasend: " << APSta.time_staDataSend/1000.0 << "\tloss: " << APSta.dropped_ha*1.0/APSta.generated_ha << "\tlatency: " << APdelavg << "\tampdu: "
			 << accumulate(APSta.apmdu_length.begin(), APSta.apmdu_length.end(), 0)*1.0/(APSta.apmdu_length.size())  << endl;


	for (int i=0;i<nRAStas;i++){
		total_hapFrames += RAStas[i].hap_frames_sent;
		total_vidFrames += RAStas[i].vid_frames_sent;
		total_kinFrames += APSta_kinFramesSent[i];
	}

	throughput_file << "STA: " << nRAStas << "\tHapFrames: " << total_hapFrames << "\tVidFrames: " << total_vidFrames << "\tKinFrames: " << total_kinFrames << endl;
	throughput = (total_hapFrames*PACKET_SIZE_BWD_HA+total_kinFrames*PACKET_SIZE_FWD_HA+total_vidFrames*PACKET_SIZE_BWD_VI)*8.0/MAX_SIMULATION_TIME_US;
	throughput_file << "STA: " << nRAStas << "\tThroughput: " << throughput << endl;


	vid_delay_file << "Total haptic frames: " << total_hap_frames << "\tTotal kin. frames: " << total_kin_frames << "\tTotal video fragments: " << total_vid_fragments << endl;
	vid_delay_file << "Per source throughput:  " <<
			(total_hap_frames*PACKET_SIZE_BWD_HA+total_kin_frames*PACKET_SIZE_FWD_HA+total_vid_fragments*FRAGMENT_SIZE)*8.0/(MAX_SIMULATION_TIME_US*nRAStas) << endl;


	vid_delay_file << "AP Inter-access time: " << accumulate(APSta.interAccess.begin(), APSta.interAccess.end(), 0)*1.0/(APSta.interAccess.size()*1000.0) << endl;
	vid_delay_file << "AP Mean AMPDU length: " << accumulate(APSta.ampduLength_kin.begin(), APSta.ampduLength_kin.end(), 0)*1.0/(APSta.ampduLength_kin.size()) << endl;

		//-------------------------- END OF PACKAGE 6 --------------------------//

	for (int i=0;i<nRAStas;i++){
		vid_delay_file << "STA: " << i << " Inter-access time: " << accumulate(RAStas[i].interAccess_ha.begin(),
				RAStas[i].interAccess_ha.end(), 0)*1.0/(RAStas[i].interAccess_ha.size()*1000.0) << endl;
		vid_delay_file << "STA: " << i << " Mean AMPDU length: " << accumulate(RAStas[i].ampduLength_ha.begin(),
						RAStas[i].ampduLength_ha.end(), 0)*1.0/(RAStas[i].ampduLength_ha.size()) << endl;
		RAStas[i].frames_sent=0;
		RAStas[i].fragments_sent=0;
		RAStas[i].hap_frames_sent=0;
		RAStas[i].vid_frames_sent=0;
		RAStas[i].accessdelay.clear();
		RAStas[i].sampleAccessDelay.clear();
		RAStas[i].sampleAccessDelayVid.clear();
		RAStas[i].delaysList.VI.clear();
		RAStas[i].delaysList.HA.clear();
		RAStas[i].interAccess_ha.clear();
		RAStas[i].interAccess_ha.clear();
		RAStas[i].ampduLength_ha.clear();
	}
	APSta.ampduLength_kin.clear();
	APSta.delaysList.HA.clear();
	APSta.sampleAccessDelay.clear();
	APSta.interAccess.clear();
	APSta.interAccess_ha.clear();
	APSta.interAccess_ha_vid.clear();
	AP_accessTime.clear();
	AP_interAccess.clear();
	APSta_kinFramesSent.clear();
	APSta.accessdelay.clear();
	ulofdma_duration.clear();
	dlofdma_duration.clear();
	ul_ofdma_dur.clear();
	ul_ofdma_data.clear();
	ul_ofdma_overhead.clear();
//	APdelays.clear();


	vid_delay_file << "\n\nAP inter-access time (not preceded by video) right after successive collisions\n 0: " <<
		accumulate(access_collision_0.begin(), access_collision_0.end(), 0.0)*1.0/(access_collision_0.size()*1000) << "\tlen: " << access_collision_0.size() <<
		"\n1: " << accumulate(access_collision_1.begin(), access_collision_1.end(), 0.0)*1.0/(access_collision_1.size()*1000) << "\tlen: " << access_collision_1.size() <<
		"\n2: " << accumulate(access_collision_2.begin(), access_collision_2.end(), 0.0)*1.0/(access_collision_2.size()*1000) << "\tlen: " << access_collision_2.size() <<
		"\n3: " << accumulate(access_collision_3.begin(), access_collision_3.end(), 0.0)*1.0/(access_collision_3.size()*1000) << "\tlen: " << access_collision_3.size() << endl;

	vid_delay_file << "\n\nAP inter-access time (preceded by video) right after successive collisions\n 0: " <<
			accumulate(access_collision_vid_0.begin(), access_collision_vid_0.end(), 0.0)*1.0/(access_collision_vid_0.size()*1000) << "\tlen: " << access_collision_vid_0.size() <<
			"\n1: " << accumulate(access_collision_vid_1.begin(), access_collision_vid_1.end(), 0.0)*1.0/(access_collision_vid_1.size()*1000) << "\tlen: " << access_collision_vid_1.size() <<
			endl;

	temp = std::string("./ResultsFiles/Global//access_collision_0.txt");
		file.open(temp);
		for (const auto &e : access_collision_0)
			file << e << "\n";
		file.close();

	temp = std::string("./ResultsFiles/Global/access_collision_1.txt");
	file.open(temp);
	for (const auto &e : access_collision_1)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Global/access_collision_2.txt");
	file.open(temp);
	for (const auto &e : access_collision_2)
		file << e << "\n";
	file.close();

	temp = std::string("./ResultsFiles/Global/access_collision_3.txt");
		file.open(temp);
		for (const auto &e : access_collision_3)
			file << e << "\n";
		file.close();

	access_collision_0.clear();
	access_collision_1.clear();
	access_collision_2.clear();
	access_collision_3.clear();


	global_file.close();
	global_buffer.close();
	frag_thresh_file.close();
	vid_metadata_file.close();
	lostPackFile.close();
	time_track.close();
	throughput_file.close();
	ofdma_track.close();
	video_file.close();
	sta_file.close();
	temp_file.close();
	hap_delay_p_file.close();
	vid_delay_p_file.close();
	kin_delay_p_file.close();
	APSta.dropped_ha=0;
	APSta.time_collision=0;
	APSta.time_idle=0;
	APSta.time_send=0;
	APSta.time_staSend=0;
	APSta.time_dataSend=0;
	APSta.time_staDataSend=0;
	total_hapFrames = 0;
	total_vidFrames = 0;
	total_kinFrames = 0;
	throughput=0;
	vi_edca_count=0;
	vi_ofdma_count=0;
	numCollisions=0;
	numVidCollisions=0;
	APSta.apmdu_length.clear();
	ulofdmadelay_sta.clear();
	ulofdmadelay_ap.clear();
	nonulofdmadelay_sta.clear();
	nonulofdmadelay_ap.clear();
	otherdelay.clear();

	return result;

}
