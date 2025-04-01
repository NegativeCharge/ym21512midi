/*
ym21512midi.c
A revised conversion of the VB.NET code to C.
Compile with a C99 compiler (e.g., MSVC or gcc).
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

/* --- Type definitions --- */

typedef struct {
    int AR;
    int D1R;
    int D2R;
    int RR;
    int D1L;
    int TL;
    int KS;
    int MUL;
    int DT1;
    int DT2;
    int AME;
} Operator_Struct;

typedef struct {
    char Name[64];    // allocated space for instrument name
    int LFRQ;
    int AMD;
    int PMD;
    int WF;
    int NFRQ;
    int PAN;
    int FL;
    int CON;
    int AMS;
    int PMS;
    int SLOT;
    int NE;
    Operator_Struct Op[4];
} Voice_Struct;

typedef struct {
    int VolumeChangeAmount;
    Voice_Struct Voice;
} CurrVoice_Struct;

/* --- Global variables --- */
int Debug = 0;

FILE* in_file = NULL;
FILE* out_file_midi = NULL;
FILE* out_file_syx = NULL;
FILE* out_file_opm = NULL;

int filepos = 0;
int filelength = 0;
uint8_t d[4] = { 0,0,0,0 };
int delay_val = 0;
int ym_reg = 0;
int ym_val = 0;

int Note[8] = { -2,-2,-2,-2,-2,-2,-2,-2 };
int Note_Old[8];
int NoteOn[8] = { 0,0,0,0,0,0,0,0 };
int NoteOn_Old[8] = { 0,0,0,0,0,0,0,0 };
int SlotArr[8] = { 0,0,0,0,0,0,0,0 };
int KF[8] = { -2,-2,-2,-2,-2,-2,-2,-2 };
int KF_old[8] = { -1,-1,-1,-1,-1,-1,-1,-1 };

int MIDIByteCount = 0;

uint8_t Registers[256] = { 0 };

int AMD_val = 0;
int PMD_val = 0;
int RegisterChanged = 0;

CurrVoice_Struct CurrentVoice[8];
Voice_Struct* Voices = NULL;
int VoicesCount = 0;
int VoiceID[8] = { -2,-2,-2,-2,-2,-2,-2,-2 };
int VoiceID_old[8] = { -1,-1,-1,-1,-1,-1,-1,-1 };
int VolumeChangeAmount_old[8] = { -1,-1,-1,-1,-1,-1,-1,-1 };
int TL_Tol = 0;
double MaxVol = 0;
double Gain = 1.0;
double BPM = 120;
int TQN = 96;

/* --- Function prototypes --- */
int KeyCodeToMIDINote(int data, int adjustOctave);

/* --- Utility Functions --- */
static int Carrier(int alg, int op) {
    int c = 0;
    if (op == 0) {           // M1
        if (alg == 7) c = 1;
    }
    else if (op == 2) {    // C1
        if (alg >= 4 && alg <= 7) c = 1;
    }
    else if (op == 1) {    // M2
        if (alg >= 5 && alg <= 7) c = 1;
    }
    else if (op == 3) {    // C2
        c = 1;
    }
    return c;
}

static int BytesToInt32(uint8_t* bytes) {
    return ((uint32_t)bytes[3] << 24) | ((uint32_t)bytes[2] << 16) | ((uint32_t)bytes[1] << 8) | ((uint32_t)bytes[0]);
}

static int BytesToInt16(uint8_t* b) {
    int v = b[1];
    v = (v << 8) | b[0];
    return v;
}

static void BytesToText(uint8_t* b, int l, char* out_str, size_t outSize) {
    int i;
    if (l + 1 > (int)outSize) l = (int)outSize - 1;
    for (i = 0; i < l; i++) {
        out_str[i] = (char)b[i];
    }
    out_str[l] = '\0';
}

/* --- MIDI Output --- */
static void Send_Midi(int Command, int Param1, int Param2) {
    uint8_t t[4] = { 0,0,0,0 };
    int delay2 = 0;
    double delay3 = 0;

    /* Calculate delay ticks using the VB formula */
    delay3 = 44100.0 / TQN;
    delay3 = delay3 * 60 / BPM;
    delay3 = delay_val / delay3;
    delay2 = (int)delay3;

    t[0] = (delay2 >> 21) & 127;
    t[1] = (delay2 >> 14) & 127;
    t[2] = (delay2 >> 7) & 127;
    t[3] = delay2 & 127;

    if (t[0] != 0) {
        fputc(t[0] | 128, out_file_midi);
        MIDIByteCount++;
    }
    if (t[1] != 0) {
        fputc(t[1] | 128, out_file_midi);
        MIDIByteCount++;
    }
    if (t[2] != 0) {
        fputc(t[2] | 128, out_file_midi);
        MIDIByteCount++;
    }
    fputc(t[3], out_file_midi);
    MIDIByteCount++;

    delay_val = 0;

    if (Command != -1) {
        fputc(Command, out_file_midi);
        MIDIByteCount++;
    }
    if (Param1 != -1) {
        fputc(Param1, out_file_midi);
        MIDIByteCount++;
    }
    if (Param2 != -1) {
        fputc(Param2, out_file_midi);
        MIDIByteCount++;
    }
}

static void AddVoice(Voice_Struct v) {
    Voice_Struct* temp = (Voice_Struct*)realloc(Voices, ((unsigned long long)(VoicesCount) + 1) * sizeof(Voice_Struct));
    if (temp == NULL) {
        fprintf(stderr, "Memory allocation failed in AddVoice()\n");
        return;
    }

    Voices = temp;
    Voices[VoicesCount] = v;
    VoicesCount++;
}

static int CompareVoice(Voice_Struct v1, Voice_Struct v2) {
    int op;
    if (v1.LFRQ != v2.LFRQ) return 0;
    if (v1.AMD != v2.AMD) return 0;
    if (v1.PMD != v2.PMD) return 0;
    if (v1.WF != v2.WF) return 0;
    if (v1.NFRQ != v2.NFRQ) return 0;
    if (v1.PAN != v2.PAN) return 0;
    if (v1.FL != v2.FL) return 0;
    if (v1.CON != v2.CON) return 0;
    if (v1.AMS != v2.AMS) return 0;
    if (v1.PMS != v2.PMS) return 0;
    if (v1.SLOT != v2.SLOT) return 0;
    if (v1.NE != v2.NE) return 0;

    for (op = 0; op < 4; op++) {
        if (v1.Op[op].AR != v2.Op[op].AR) return 0;
        if (v1.Op[op].D1R != v2.Op[op].D1R) return 0;
        if (v1.Op[op].D2R != v2.Op[op].D2R) return 0;
        if (v1.Op[op].RR != v2.Op[op].RR) return 0;
        if (v1.Op[op].D1L != v2.Op[op].D1L) return 0;
        if (abs(v1.Op[op].TL - v2.Op[op].TL) > TL_Tol) return 0;
        if (v1.Op[op].KS != v2.Op[op].KS) return 0;
        if (v1.Op[op].MUL != v2.Op[op].MUL) return 0;
        if (v1.Op[op].DT1 != v2.Op[op].DT1) return 0;
        if (v1.Op[op].DT2 != v2.Op[op].DT2) return 0;
        if (v1.Op[op].AME != v2.Op[op].AME) return 0;
    }
    return 1;
}

static int FindVoice(Voice_Struct v) {
    int i;
    int found = -1;
    if (VoicesCount > 0) {
        for (i = 0; i < VoicesCount; i++) {
            if (CompareVoice(v, Voices[i])) {
                found = i;
                break;
            }
        }
    }
    if (found == -1) {
        AddVoice(v);
        found = VoicesCount - 1;
    }
    return found;
}

/* --- Get current voice from register values --- */
static CurrVoice_Struct GetCurrentVoice(int chan) {
    int op, TL_Min;
    CurrVoice_Struct curr_voice = {0};
    curr_voice.Voice.Name[0] = '\0';

    curr_voice.Voice.AMS = Registers[0x38 + chan] & 3;
    curr_voice.Voice.PMS = (Registers[0x38 + chan] >> 4) & 7;

    if (curr_voice.Voice.AMS != 0 || curr_voice.Voice.PMS != 0) {
        curr_voice.Voice.LFRQ = Registers[0x18];
        curr_voice.Voice.AMD = AMD_val;
        curr_voice.Voice.PMD = PMD_val;
    }
    else {
        curr_voice.Voice.LFRQ = 0;
        curr_voice.Voice.AMD = 0;
        curr_voice.Voice.PMD = 0;
    }

    curr_voice.Voice.WF = Registers[0x1B] & 3;
    curr_voice.Voice.NFRQ = Registers[0x0F] & 127;
    curr_voice.Voice.PAN = Registers[0x20 + chan] & 192;
    curr_voice.Voice.FL = (Registers[0x20 + chan] >> 3) & 7;
    curr_voice.Voice.CON = Registers[0x20 + chan] & 7;
    curr_voice.Voice.SLOT = Registers[0x8] & 120;
    curr_voice.Voice.NE = Registers[0x0F] & 128;

    for (op = 0; op < 4; op++) {
        curr_voice.Voice.Op[op].AR = Registers[0x80 + chan + (op * 8)] & 31;
        curr_voice.Voice.Op[op].D1R = Registers[0xA0 + chan + (op * 8)] & 31;
        curr_voice.Voice.Op[op].D2R = Registers[0xC0 + chan + (op * 8)] & 31;
        curr_voice.Voice.Op[op].RR = Registers[0xE0 + chan + (op * 8)] & 15;
        curr_voice.Voice.Op[op].D1L = (Registers[0xE0 + chan + (op * 8)] >> 4) & 15;
        curr_voice.Voice.Op[op].TL = Registers[0x60 + chan + (op * 8)] & 127;
        curr_voice.Voice.Op[op].KS = (Registers[0x80 + chan + (op * 8)] >> 6) & 3;
        curr_voice.Voice.Op[op].MUL = Registers[0x40 + chan + (op * 8)] & 15;
        curr_voice.Voice.Op[op].DT1 = (Registers[0x40 + chan + (op * 8)] >> 4) & 7;
        curr_voice.Voice.Op[op].DT2 = (Registers[0xC0 + chan + (op * 8)] >> 6) & 3;
        curr_voice.Voice.Op[op].AME = Registers[0xA0 + chan + (op * 8)] & 128;
    }

    TL_Min = 255;
    for (op = 0; op < 4; op++) {
        if (Carrier(curr_voice.Voice.CON, op)) {
            if (curr_voice.Voice.Op[op].TL < TL_Min)
                TL_Min = curr_voice.Voice.Op[op].TL;
        }
    }

    if (TL_Min <= 127) {
        for (op = 0; op < 4; op++) {
            if (Carrier(curr_voice.Voice.CON, op)) {
                curr_voice.Voice.Op[op].TL -= TL_Min;
            }
        }
        curr_voice.VolumeChangeAmount = TL_Min;
    }
    else {
        curr_voice.VolumeChangeAmount = 0;
        printf("Did not find minimum TL\n");
    }

    return curr_voice;
}

/* --- Send YM register commands --- */
static void SendYM() {
    int KF_PB, Chan;
    double Vol;

    Registers[ym_reg] = ym_val;

    if (ym_reg == 0x8) {
        Chan = ym_val & 0x7;
        SlotArr[Chan] = (ym_val & 0x78) >> 3;
        NoteOn_Old[Chan] = NoteOn[Chan];
        if (SlotArr[Chan] != 0) {
            VolumeChangeAmount_old[Chan] = CurrentVoice[Chan].VolumeChangeAmount;
            CurrentVoice[Chan] = GetCurrentVoice(Chan);
            VoiceID_old[Chan] = VoiceID[Chan];
            VoiceID[Chan] = FindVoice(CurrentVoice[Chan].Voice);
            if (VoiceID_old[Chan] != VoiceID[Chan]) {
                Send_Midi(0xC0 + Chan, VoiceID[Chan], -1);
            }
            if (VolumeChangeAmount_old[Chan] != CurrentVoice[Chan].VolumeChangeAmount) {
                Vol = -(CurrentVoice[Chan].VolumeChangeAmount * 0.75);
                Vol = pow(10, Vol / 40.0) * 127;
                Vol = Vol * Gain;
                if (Vol > MaxVol) MaxVol = Vol;
                if (Vol > 127) Vol = 127;
                if (Vol < 0) Vol = 0;
                Send_Midi(0xB0 + Chan, 7, (int)Vol);
            }
            RegisterChanged = 0;
            NoteOn[Chan] = 1;
        }
        else {
            NoteOn[Chan] = 0;
        }
        if (NoteOn_Old[Chan] != NoteOn[Chan]) {
            if (NoteOn[Chan]) {
                if (Note[Chan] >= 0)
                    Send_Midi(0x90 + Chan, Note[Chan], 127);
                else
                    printf("Key on occurred before note was set!\n");
            }
            else {
                if (Note[Chan] >= 0)
                    Send_Midi(0x80 + Chan, Note[Chan], 0);
            }
        }
    }
    else if ((ym_reg >= 0x28) && (ym_reg <= 0x2F)) {
        Chan = ym_reg & 0x7;
        Note_Old[Chan] = Note[Chan];
        Note[Chan] = KeyCodeToMIDINote(ym_val, 0);
        if (NoteOn[Chan] && (Note[Chan] != Note_Old[Chan])) {
            if (Note_Old[Chan] >= 0)
                Send_Midi(0x80 + Chan, Note_Old[Chan], 0);
            Send_Midi(0x90 + Chan, Note[Chan], 127);
        }
    }
    else if ((ym_reg >= 0x30) && (ym_reg <= 0x37)) {
        Chan = ym_reg & 0x7;
        KF[Chan] = ym_val >> 2;
        if (KF[Chan] != KF_old[Chan]) {
            KF_old[Chan] = KF[Chan];
            KF_PB = KF[Chan] * 64 + 8192;
            Send_Midi(0xE0 + Chan, KF_PB & 0x7F, KF_PB >> 7);
        }
    }
    else if (ym_reg == 0x19) {
        if ((ym_val & 0x80) == 0) {
            AMD_val = ym_val & 127;
        }
        else {
            PMD_val = ym_val & 127;
        }
        RegisterChanged = 1;
    }
    else if ((ym_reg == 0x18) || (ym_reg == 0x1B) ||
        ((ym_reg >= 0x20) && (ym_reg <= 0xFF))) {
        RegisterChanged = 1;
    }
}

/* --- Parse one command from input file --- */
static void Parse() {
    if (fread(d, 1, 1, in_file) != 1) return;
    if (Debug) printf("Filepos: 0x%x, Register: 0x%x, Total length: 0x%x\n", filepos, d[0], filelength);
    filepos++;

    if (((d[0] >= 0x30) && (d[0] <= 0x3F)) || (d[0] == 0x4F) || (d[0] == 0x50)) {
        fread(d, 1, 1, in_file); filepos++;
    }
    else if (((d[0] >= 0x40) && (d[0] <= 0x4E)) ||
        ((d[0] >= 0x51) && (d[0] <= 0x53)) ||
        ((d[0] >= 0x55) && (d[0] <= 0x5F)) ||
        ((d[0] >= 0xA0) && (d[0] <= 0xBF))) {
        fread(d, 1, 2, in_file); filepos += 2;
    }
    else if (((d[0] >= 0xC0) && (d[0] <= 0xDF)) || (d[0] == 0x64)) {
        fread(d, 1, 3, in_file); filepos += 3;
    }
    else if ((d[0] >= 0xE0) && (d[0] <= 0xEF)) {
        fread(d, 1, 4, in_file); filepos += 4;
    }
    else if (d[0] == 0x54) {
        fread(d, 1, 2, in_file); filepos += 2;
        ym_reg = d[0];
        ym_val = d[1];
        SendYM();
    }
    else if (d[0] == 0x61) {
        fread(d, 1, 2, in_file); filepos += 2;
        delay_val += BytesToInt16(d);
    }
    else if (d[0] == 0x62) {
        fread(d, 1, 1, in_file); filepos++;
        delay_val += 735;
    }
    else if (d[0] == 0x63) {
        fread(d, 1, 1, in_file); filepos++;
        delay_val += 882;
    }
    else if (d[0] == 0x66) {
        filepos = filelength;
    }
    else if (d[0] == 0x67) {
        fread(d, 1, 1, in_file); filepos++;     // 0x66
        fread(d, 1, 1, in_file); filepos++;     // tt
        fread(d, 1, 4, in_file); filepos += 4;  // ss ss ss ss
        uint32_t extra = BytesToInt32(d);
        filepos += extra;
        if (filepos < 0) filepos = filelength;
        fseek(in_file, filepos, SEEK_SET);
    }
    else if (d[0] == 0x68) {
        fread(d, 1, 1, in_file); filepos++;
        fread(d, 1, 1, in_file); filepos++;
        fread(d, 1, 3, in_file); filepos += 3;
        fread(d, 1, 3, in_file); filepos += 3;
        fread(d, 1, 3, in_file); filepos += 3;
    }
    else if ((d[0] >= 0x70) && (d[0] <= 0x8F)) {
        delay_val += d[0] & 15;
    }
    else if ((d[0] == 0x90) || (d[0] == 0x91) || (d[0] == 0x95)) {
        fread(d, 1, 4, in_file); filepos += 4;
    }
    else if (d[0] == 0x92) {
        fread(d, 1, 1, in_file); filepos++;
        fread(d, 1, 4, in_file); filepos += 4;
    }
    else if (d[0] == 0x93) {
        fread(d, 1, 1, in_file); filepos++;
        fread(d, 1, 4, in_file); filepos += 4;
        fread(d, 1, 1, in_file); filepos++;
        fread(d, 1, 4, in_file); filepos += 4;
    }
    else if (d[0] == 0x94) {
        fread(d, 1, 1, in_file); filepos++;
    }
}

/* --- Revised Parse Loop: process until end of file --- */
static void ParseLoop() {
    while (filepos < filelength) {
        Parse();
    }
    fclose(in_file);
}

/* --- Checksum --- */
static uint8_t Checksum(uint8_t* data, int len) {
    int check = 0;
    for (int i = 0; i < len; i++) {
        check += data[i];
    }
    check = ((~check) + 1) & 127;
    return (uint8_t)check;
}

/* --- Convert Voice to FB01 format --- */
static void Voice_to_FB01(Voice_Struct Voice, uint8_t* fb01_voice) {
    int frlp, op2, car, TL;
    uint8_t default_fb01[64] = { 83,105,110,101,87,97,118,0,205,128,0,120,0,0,64,0,
       127,0,0,1,31,128,0,15,127,0,0,1,31,128,0,15,
       127,0,0,1,31,128,0,15,0,0,0,1,31,128,0,15,
       0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
    memcpy(fb01_voice, default_fb01, 64);

    if (strlen(Voice.Name) > 0) {
        for (frlp = 0; frlp < 7; frlp++) {
            if (frlp < (int)strlen(Voice.Name))
                fb01_voice[frlp] = (uint8_t)Voice.Name[frlp];
            else
                fb01_voice[frlp] = ' ';
        }
        fb01_voice[7] = 0;
        fb01_voice[8] = Voice.LFRQ & 0xFF;
        fb01_voice[9] = Voice.AMD & 127;
        fb01_voice[10] = Voice.PMD & 127;
        fb01_voice[11] = Voice.SLOT & 120;
        fb01_voice[12] = ((Voice.FL & 7) << 3) + (Voice.CON & 7);
        fb01_voice[13] = (Voice.AMS & 3) + ((Voice.PMS & 7) << 4);
        fb01_voice[14] = (Voice.WF & 3) << 5;
        fb01_voice[15] = 0;

        for (frlp = 0; frlp < 4; frlp++) {
            car = Carrier(Voice.CON & 7, frlp) ? 1 : 0;
            TL = Voice.Op[frlp].TL;
            if (!car) TL -= 8;
            if (TL < 0) { printf("TL was less than 0\n"); TL = 0; }
            if (frlp == 0)
                op2 = 0;
            else if (frlp == 1)
                op2 = 2;
            else if (frlp == 2)
                op2 = 1;
            else
                op2 = 3;
            fb01_voice[op2 * 8 + 16] = TL & 127;
            fb01_voice[op2 * 8 + 17] = 0;
            fb01_voice[op2 * 8 + 18] = 0;
            fb01_voice[op2 * 8 + 19] = (Voice.Op[frlp].MUL & 15) + ((Voice.Op[frlp].DT1 & 7) << 4);
            fb01_voice[op2 * 8 + 20] = (Voice.Op[frlp].AR & 31) + ((Voice.Op[frlp].KS & 3) << 6);
            fb01_voice[op2 * 8 + 21] = (car << 7) + (Voice.Op[frlp].D1R & 31);
            fb01_voice[op2 * 8 + 22] = (Voice.Op[frlp].D2R & 31) + ((Voice.Op[frlp].DT2 & 3) << 6);
            fb01_voice[op2 * 8 + 23] = (Voice.Op[frlp].RR & 15) + ((Voice.Op[frlp].D1L & 15) << 4);
        }
        for (frlp = 48; frlp < 58; frlp++) {
            fb01_voice[frlp] = 0;
        }
        fb01_voice[58] = 0;
        fb01_voice[59] = 2;
        fb01_voice[60] = 0;
        fb01_voice[61] = 0;
        fb01_voice[62] = 0;
        fb01_voice[63] = 0;
    }
}

/* --- Write Instruments (SYX and OPM) --- */
static void WriteInsts(const char* basepath) {
    uint8_t syx_buff[128] = { 0 };
    uint8_t fb01_voice[64] = { 0 };
    int frlp, frlp2, length;
    char st[128];

    fputc(0xF0, out_file_syx);
    fputc(0x43, out_file_syx);
    fputc(0x75, out_file_syx);
    fputc(0, out_file_syx);
    fputc(0, out_file_syx);
    fputc(0, out_file_syx);
    fputc(0, out_file_syx);

    memset(syx_buff, 0, sizeof(syx_buff));
    syx_buff[0] = 'O' & 0xF;
    syx_buff[1] = ('O' & 0xF0) >> 4;
    syx_buff[2] = 'P' & 0xF;
    syx_buff[3] = ('P' & 0xF0) >> 4;
    syx_buff[4] = 'M' & 0xF;
    syx_buff[5] = ('M' & 0xF0) >> 4;
    syx_buff[6] = ' ' & 0xF;
    syx_buff[7] = (' ' & 0xF0) >> 4;
    syx_buff[8] = 'B' & 0xF;
    syx_buff[9] = ('B' & 0xF0) >> 4;
    syx_buff[10] = 'a' & 0xF;
    syx_buff[11] = ('a' & 0xF0) >> 4;
    syx_buff[12] = 'n' & 0xF;
    syx_buff[13] = ('n' & 0xF0) >> 4;
    syx_buff[14] = 'k' & 0xF;
    syx_buff[15] = ('k' & 0xF0) >> 4;

    length = (int)sizeof(syx_buff);
    fputc((length & 0xFF00) >> 8, out_file_syx);
    fputc(length & 0xFF, out_file_syx);
    fwrite(syx_buff, 1, length, out_file_syx);
    fputc(Checksum(syx_buff, length), out_file_syx);

    fprintf(out_file_opm, "// Created by ym21512midi.c\n\n");

    for (frlp = 0; frlp < 48; frlp++) {
        if (frlp < VoicesCount) {
            /* Use secure version of snprintf */
            sprintf_s(Voices[frlp].Name, sizeof(Voices[frlp].Name), "Inst %d", frlp);
            Voice_to_FB01(Voices[frlp], fb01_voice);
            fprintf(out_file_opm, "@:%d Inst_%d\n", frlp, frlp);
            fprintf(out_file_opm, "//  LFRQ AMD PMD WF NFRQ\n");
            fprintf(out_file_opm, "LFO: %d  %d  %d  %d  %d\n", Voices[frlp].LFRQ, Voices[frlp].AMD, Voices[frlp].PMD, Voices[frlp].WF, Voices[frlp].NFRQ);
            fprintf(out_file_opm, "// PAN FL CON AMS PMS SLOT NE\n");
            fprintf(out_file_opm, "CH: %d  %d  %d  %d  %d  %d  %d\n", 64, Voices[frlp].FL, Voices[frlp].CON, Voices[frlp].AMS, Voices[frlp].PMS, Voices[frlp].SLOT, Voices[frlp].NE);
            fprintf(out_file_opm, "//  AR D1R D2R RR D1L  TL KS MUL DT1 DT2 AMS-EN\n");
            for (frlp2 = 0; frlp2 < 4; frlp2++) {
                int opLabel;
                if (frlp2 == 0) { opLabel = 0; strcpy_s(st, sizeof(st), "M1: "); }
                else if (frlp2 == 1) { opLabel = 2; strcpy_s(st, sizeof(st), "C1: "); }
                else if (frlp2 == 2) { opLabel = 1; strcpy_s(st, sizeof(st), "M2: "); }
                else { opLabel = 3; strcpy_s(st, sizeof(st), "C2: "); }
                fprintf(out_file_opm, "%s%d  %d  %d  %d  %d  %d  %d  %d  %d  %d  %d\n", st,
                    Voices[frlp].Op[opLabel].AR,
                    Voices[frlp].Op[opLabel].D1R,
                    Voices[frlp].Op[opLabel].D2R,
                    Voices[frlp].Op[opLabel].RR,
                    Voices[frlp].Op[opLabel].D1L,
                    Voices[frlp].Op[opLabel].TL,
                    Voices[frlp].Op[opLabel].KS,
                    Voices[frlp].Op[opLabel].MUL,
                    Voices[frlp].Op[opLabel].DT1,
                    Voices[frlp].Op[opLabel].DT2,
                    Voices[frlp].Op[opLabel].AME);
            }
            fprintf(out_file_opm, "\n");
        }
        else {
            if (VoicesCount > 0)
                Voice_to_FB01(Voices[VoicesCount - 1], fb01_voice);
        }

        for (frlp2 = 0; frlp2 < 64; frlp2++) {
            syx_buff[frlp2 * 2] = fb01_voice[frlp2] & 0xF;
            syx_buff[frlp2 * 2 + 1] = (fb01_voice[frlp2] & 0xF0) >> 4;
        }
        length = (int)sizeof(syx_buff);
        fputc((length & 0xFF00) >> 8, out_file_syx);
        fputc(length & 0xFF, out_file_syx);
        fwrite(syx_buff, 1, length, out_file_syx);
        fputc(Checksum(syx_buff, length), out_file_syx);
    }
    fputc(0xF7, out_file_syx);
}

static void WriteMIDIHeader() {
    long currentPos = ftell(out_file_midi);
    /* The MIDI file begins with a 14-byte header and an 8-byte track header.
       Update the 4-byte track length at offset 18. */
    fseek(out_file_midi, 18, SEEK_SET);
    uint8_t trackLength[4] = {0};
    trackLength[0] = (MIDIByteCount >> 24) & 0xFF;
    trackLength[1] = (MIDIByteCount >> 16) & 0xFF;
    trackLength[2] = (MIDIByteCount >> 8) & 0xFF;
    trackLength[3] = MIDIByteCount & 0xFF;
    fwrite(trackLength, 1, 4, out_file_midi);
    fseek(out_file_midi, currentPos, SEEK_SET);
}

/* --- KeyCode to MIDI Note Conversion --- */
int KeyCodeToMIDINote(int data, int adjustOctave) {
    int FNum = data & 0xF;
    int Octave = (data & 0x70) >> 4;
    if (adjustOctave)
        Octave = Octave - 1;
    int NoteVal = 0;
    if (FNum == 0) { NoteVal = 61; }
    else if (FNum == 1) { NoteVal = 62; }
    else if (FNum == 2) { NoteVal = 63; }
    else if (FNum == 3) { NoteVal = 0; }
    else if (FNum == 4) { NoteVal = 64; }
    else if (FNum == 5) { NoteVal = 65; }
    else if (FNum == 6) { NoteVal = 66; }
    else if (FNum == 7) { NoteVal = 0; }
    else if (FNum == 8) { NoteVal = 67; }
    else if (FNum == 9) { NoteVal = 68; }
    else if (FNum == 10) { NoteVal = 69; }
    else if (FNum == 11) { NoteVal = 0; }
    else if (FNum == 12) { NoteVal = 70; }
    else if (FNum == 13) { NoteVal = 71; }
    else if (FNum == 14) { NoteVal = 72; }
    else if (FNum == 15) { NoteVal = 0; }
    if (NoteVal != 0)
        NoteVal += (Octave - 4) * 12;
    else
        printf("Note value was invalid\n");
    if (NoteVal < 0) {
        printf("Note value was less than 0\n");
        NoteVal = 0;
    }
    return NoteVal;
}

static void parseArguments(int argc, char* argv[], char* inputPath) {
    TL_Tol = 10;
    Gain = 1.0;
    BPM = 120;
    TQN = 96;
    Debug = 0;
    inputPath[0] = '\0';

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0) {
            Debug = 1;
        }
        else if (strcmp(argv[i], "-tl_tol") == 0 && i + 1 < argc) {
            TL_Tol = atoi(argv[++i]);
        }
        else if (strcmp(argv[i], "-gain") == 0 && i + 1 < argc) {
            Gain = atof(argv[++i]);
        }
        else if (strcmp(argv[i], "-bpm") == 0 && i + 1 < argc) {
            BPM = atof(argv[++i]);
        }
        else if (strcmp(argv[i], "-tqn") == 0 && i + 1 < argc) {
            TQN = atoi(argv[++i]);
        }
        else if (argv[i][0] == '-') {
            printf("Error: Unknown parameter %s\n", argv[i]);
            exit(1);
        }
        else {
            strncpy_s(inputPath, 256, argv[i], _TRUNCATE);
        }
    }
}

/* --- Main --- */
int main(int argc, char* argv[]) {
    char inputPath[256];
    char outPath[256];
    char basePath[256];
    int BPM_Period;
    int frlp;
    double tempD;

    if (argc < 2) {
        printf("Usage: %s [-d] [-tl_tol <value>] [-gain <value>] [-bpm <value>] [-tqn <value>] <input VGM file>\n", argv[0]);
        return 1;
    }

    parseArguments(argc, argv, inputPath);

    if (strlen(inputPath) == 0) {
        printf("Error: Input file path is required\n");
        return 1;
    }
    
    if (fopen_s(&in_file, inputPath, "rb") != 0 || in_file == NULL) {
        printf("Cannot open input file %s\n", inputPath);
        return 1;
    }

    if (fread(d, 1, 4, in_file) != 4) { fclose(in_file); return 1; }
    char header[5];
    BytesToText(d, 4, header, sizeof(header));
    if (strcmp(header, "Vgm ") != 0) {
        fclose(in_file);
        printf("Not a VGM file.\n");
        return 1;
    }

    if (fread(d, 1, 4, in_file) != 4) { fclose(in_file); return 1; }
    filelength = BytesToInt32(d) + 4;
    fseek(in_file, 0, SEEK_END);
    long actualLength = ftell(in_file);
    if (filelength > actualLength) {
        fclose(in_file);
        printf("File length mismatch.\n");
        return 1;
    }
    printf("File length is: %d bytes\n", filelength);

    fseek(in_file, 0x30, SEEK_SET);
    if (fread(d, 1, 4, in_file) != 4) { fclose(in_file); return 1; }
    tempD = BytesToInt32(d);
    if (tempD != 0)
        printf("YM2151 Frequency is: %.0f MHz\n", tempD);
    else { fclose(in_file); return 1; }

    if (fread(d, 1, 4, in_file) != 4) { fclose(in_file); return 1; }
    tempD = BytesToInt32(d);
    if (tempD == 0) tempD = 12;
    filepos = (int)tempD + 0x34;
    fseek(in_file, filepos, SEEK_SET);
    printf("Data starts at: 0x%x\n", filepos);

    delay_val = 0;

    /* Prepare output file names by stripping extension */
    char* dot = strrchr(inputPath, '.');
    if (dot) *dot = '\0';
    strncpy_s(basePath, sizeof(basePath), inputPath, _TRUNCATE);

    sprintf_s(outPath, sizeof(outPath), "%s.mid", basePath);
    if (fopen_s(&out_file_midi, outPath, "wb+") != 0 || out_file_midi == NULL) {
        printf("Cannot open output MIDI file.\n");
        return 1;
    }

    MIDIByteCount = 0;
    VoicesCount = 0;
    RegisterChanged = 0;
    Voices = NULL;
    for (frlp = 0; frlp < 8; frlp++) {
        Note_Old[frlp] = -1;
        NoteOn_Old[frlp] = 0;
        KF_old[frlp] = -1;
        VoiceID_old[frlp] = -1;
        VolumeChangeAmount_old[frlp] = -1;
        Note[frlp] = -2;
        NoteOn[frlp] = 0;
        KF[frlp] = -2;
        VoiceID[frlp] = -2;
        CurrentVoice[frlp].VolumeChangeAmount = -2;
    }
    memset(Registers, 0, sizeof(Registers));

    printf("Ticks per quarter note = %d\n", TQN);

    /* Write initial MIDI header (MThd) and a track header placeholder */
    uint8_t mthd[14] = { 'M','T','h','d', 0,0,0,6, 0,1, 0,1, (uint8_t)((TQN >> 8) & 0xFF), (uint8_t)(TQN & 0xFF) };
    fwrite(mthd, 1, 14, out_file_midi);
    uint8_t mtrk[8] = { 'M','T','r','k', 0,0,0,0 };
    fwrite(mtrk, 1, 8, out_file_midi);

    BPM_Period = 60000000 / (int)BPM;
    Send_Midi(0xFF, 0x51, 3);
    fputc((BPM_Period >> 16) & 0xFF, out_file_midi); MIDIByteCount++;
    fputc((BPM_Period >> 8) & 0xFF, out_file_midi); MIDIByteCount++;
    fputc(BPM_Period & 0xFF, out_file_midi); MIDIByteCount++;

    for (frlp = 0; frlp < 8; frlp++) {
        Send_Midi(0xE0 + frlp, 8192 & 0x7F, 8192 >> 7);
    }

    /* Process entire data block */
    ParseLoop();

    Send_Midi(0xFF, 0x2F, 0);  // End of track
    WriteMIDIHeader();         // Update the track chunk length
    fclose(out_file_midi);

    sprintf_s(outPath, sizeof(outPath), "%s.syx", basePath);
    if (fopen_s(&out_file_syx, outPath, "wb") != 0 || out_file_syx == NULL) {
        printf("Cannot open output SYX file.\n");
        return 1;
    }

    sprintf_s(outPath, sizeof(outPath), "%s.opm", basePath);
    if (fopen_s(&out_file_opm, outPath, "w") != 0 || out_file_opm == NULL) {
        printf("Cannot open output OPM file.\n");
        return 1;
    }

    WriteInsts(basePath);

    fclose(out_file_syx);
    fclose(out_file_opm);

    printf("Number of voices found: %d\n", VoicesCount);
    if (MaxVol == 0) {
        printf("Maximum volume was: 0 out of 127\n");
        printf("Gain not computed because no volume change occurred.\n");
    }
    else {
        tempD = floor(MaxVol * 1000) / 1000.0;
        printf("Maximum volume was: %.3f out of 127\n", tempD);
        tempD = floor(((127.0 / MaxVol) * Gain) * 1000) / 1000.0;
        printf("Set gain to: %.3f to get best result\n", tempD);
    }
    printf("Conversion complete\n");

    free(Voices);
    return 0;
}